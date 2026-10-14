/*
 * Smart Modeling Suite for Blockbench
 * Version 0.5.0
 *
 * Features:
 *  - Smart Mirror Modeling for cubes (X/Y/Z mirror planes)
 *  - Exact duplicate cube checker
 *  - Safe texture optimizer with exact pixel reuse + lossless solid/scaled-pattern reduction
 *  - Restore previous selection
 *  - Sticky selection mode + explicit clear button
 *  - Smart Vertex Snap with corner movement, mirror-plane alignment and edge workflows
 *  - Symmetric layered 3D blade generator for flat cube profiles
 *
 * This plugin is designed to be Minecraft-version agnostic. It works on Blockbench cubes,
 * UVs and textures rather than targeting a specific Minecraft release.
 */

(function() {
    const PLUGIN_ID = 'smart_modeling_suite';
    const VERSION = '0.5.0';
    const EPS = 1e-7;

    let actions = [];
    let listeners = [];

    const state = {
        mirrorAxis: 0,            // 0=X, 1=Y, 2=Z
        mirrorPlane: 8,
        smartMirrorEnabled: false,
        mirrorGuard: false,
        mirrorPairs: new Map(),   // uuid -> partner uuid
        mirrorSingles: new Set(), // cubes that intentionally span the mirror plane as one symmetric cube
        cubeSnapshots: new Map(), // uuid -> last transform snapshot
        knownCubeUUIDs: new Set(),
        nativeMirrorStates: new Map(), // Project object -> original native mirror state
        syncScheduled: false,
        syncTimer: null,
        forcedMirrorUUIDs: new Set(),
        mirrorAuthority: new Map(), // uuid -> {side:-1|1}; touched mirror side must remain untouched
        pendingVertexSnapAuthority: null,

        advancedVertex: {
            sourceCubeUUID: null,
            sourceVertex: null,
            sourceEdge: null,
            sourceEdgeVertexA: null,
            targetVertexA: null,
            stage: 'source_feature',
        },

        duplicateReview: null,
        duplicateReviewNode: null,
        cssHandle: null,

        stickySelection: false,
        selectionGuard: false,
        currentSelection: [],
        previousSelection: [],
        stickySelectionSnapshot: [],
        allowExplicitClear: false,
    };

    function log(...args) {
        console.log('[Smart Modeling Suite]', ...args);
    }

    function warn(...args) {
        console.warn('[Smart Modeling Suite]', ...args);
    }

    function quick(message, time = 2400) {
        if (typeof Blockbench !== 'undefined' && Blockbench.showQuickMessage) {
            Blockbench.showQuickMessage(message, time);
        } else {
            log(message);
        }
    }

    function addListener(event, fn) {
        Blockbench.on(event, fn);
        listeners.push([event, fn]);
    }

    function removeAllListeners() {
        listeners.forEach(([event, fn]) => {
            try { Blockbench.removeListener(event, fn); } catch (e) { /* ignore */ }
        });
        listeners = [];
    }

    function axisName(axis = state.mirrorAxis) {
        return ['X', 'Y', 'Z'][axis] || 'X';
    }

    function copyArray(a) {
        return Array.isArray(a) ? a.slice() : a;
    }

    function disableNativeMirrorForProject(project = (typeof Project !== 'undefined' ? Project : null)) {
        if (!project || !('mirror_modeling_enabled' in project)) return;
        if (!state.nativeMirrorStates.has(project)) {
            state.nativeMirrorStates.set(project, !!project.mirror_modeling_enabled);
        }
        project.mirror_modeling_enabled = false;
    }

    function restoreNativeMirrorStates() {
        for (const [project, enabled] of state.nativeMirrorStates) {
            try {
                if (project && 'mirror_modeling_enabled' in project) project.mirror_modeling_enabled = enabled;
            } catch (_) {}
        }
        state.nativeMirrorStates.clear();
    }

    function nearlyEqual(a, b, eps = EPS) {
        return Math.abs(a - b) <= eps;
    }

    function arraysEqualExact(a, b) {
        if (!Array.isArray(a) || !Array.isArray(b) || a.length !== b.length) return false;
        for (let i = 0; i < a.length; i++) {
            if (a[i] !== b[i]) return false;
        }
        return true;
    }

    function arraysNearlyEqual(a, b, eps = EPS) {
        if (!Array.isArray(a) || !Array.isArray(b) || a.length !== b.length) return false;
        for (let i = 0; i < a.length; i++) {
            if (!nearlyEqual(a[i], b[i], eps)) return false;
        }
        return true;
    }

    function mirrorCoordinate(value, plane) {
        return 2 * plane - value;
    }

    function mirroredTransformData(cube, axis = state.mirrorAxis, plane = state.mirrorPlane) {
        // Prefer Blockbench's own flip implementation because it already knows how
        // the current Blockbench version represents cube rotations.
        try {
            if (typeof Cube !== 'undefined' && cube && typeof cube.getSaveCopy === 'function') {
                const temp = new Cube(cube.getSaveCopy());
                if (typeof temp.flip === 'function') {
                    temp.flip(axis, plane, true);
                    return {
                        from: temp.from.slice(),
                        to: temp.to.slice(),
                        origin: temp.origin.slice(),
                        rotation: temp.rotation.slice(),
                    };
                }
            }
        } catch (e) {
            // Fall through to the math fallback below.
        }

        const from = cube.from.slice();
        const to = cube.to.slice();
        const origin = cube.origin.slice();
        const rotation = cube.rotation.slice();
        const oldFrom = cube.from[axis];
        const oldTo = cube.to[axis];
        from[axis] = mirrorCoordinate(oldTo, plane);
        to[axis] = mirrorCoordinate(oldFrom, plane);
        origin[axis] = mirrorCoordinate(cube.origin[axis], plane);

        // Fallback for older builds. For the normal Minecraft single-axis cube
        // rotations this matches Blockbench's mirrored orientation.
        for (let i = 0; i < 3; i++) {
            rotation[i] = (i === axis) ? cube.rotation[i] : -cube.rotation[i];
        }
        return { from, to, origin, rotation };
    }

    function cubeCanBeSingleSymmetricCube(cube, axis = state.mirrorAxis) {
        // A rectangular cuboid can be represented by ONE cube across the mirror plane
        // when it is not tilted around either of the two axes lying across that plane.
        // Rotation around the mirror normal itself is fine.
        for (let i = 0; i < 3; i++) {
            if (i === axis) continue;
            let r = Number(cube.rotation[i] || 0);
            r = ((r + 180) % 360 + 360) % 360 - 180;
            const ok = nearlyEqual(r, 0, 1e-5) || nearlyEqual(Math.abs(r), 180, 1e-5);
            if (!ok) return false;
        }
        return true;
    }

    function cubeLocalIntersectsPlane(cube, axis = state.mirrorAxis, plane = state.mirrorPlane) {
        const min = Math.min(cube.from[axis], cube.to[axis]);
        const max = Math.max(cube.from[axis], cube.to[axis]);
        return min <= plane + EPS && max >= plane - EPS;
    }

    function cubeLocalCrossesPlane(cube, axis = state.mirrorAxis, plane = state.mirrorPlane) {
        const min = Math.min(cube.from[axis], cube.to[axis]);
        const max = Math.max(cube.from[axis], cube.to[axis]);
        return min < plane - EPS && max > plane + EPS;
    }

    function cubeIsLocallySymmetric(cube, axis = state.mirrorAxis, plane = state.mirrorPlane) {
        return nearlyEqual(Math.abs(cube.from[axis] - plane), Math.abs(cube.to[axis] - plane), 1e-5);
    }

    function snapshotCube(cube) {
        return {
            from: cube.from.slice(),
            to: cube.to.slice(),
            origin: cube.origin.slice(),
            rotation: cube.rotation.slice(),
            inflate: Number(cube.inflate || 0),
            stretch: Array.isArray(cube.stretch) ? cube.stretch.slice() : null,
            parent: cube.parent && cube.parent.uuid ? cube.parent.uuid : cube.parent,
        };
    }

    function cubeTransformChanged(cube, snap) {
        if (!snap) return true;
        if (!arraysNearlyEqual(cube.from, snap.from, 1e-7)) return true;
        if (!arraysNearlyEqual(cube.to, snap.to, 1e-7)) return true;
        if (!arraysNearlyEqual(cube.origin, snap.origin, 1e-7)) return true;
        if (!arraysNearlyEqual(cube.rotation, snap.rotation, 1e-7)) return true;
        if (!nearlyEqual(Number(cube.inflate || 0), Number(snap.inflate || 0), 1e-7)) return true;
        if (Array.isArray(cube.stretch) || Array.isArray(snap.stretch)) {
            if (!arraysNearlyEqual(cube.stretch || [1,1,1], snap.stretch || [1,1,1], 1e-7)) return true;
        }
        const parent = cube.parent && cube.parent.uuid ? cube.parent.uuid : cube.parent;
        return parent !== snap.parent;
    }

    function cubeTransformDelta(cube, snap) {
        if (!snap) return Number.POSITIVE_INFINITY;
        let d = 0;
        for (let i = 0; i < 3; i++) {
            d += Math.abs(cube.from[i] - snap.from[i]);
            d += Math.abs(cube.to[i] - snap.to[i]);
            d += Math.abs(cube.origin[i] - snap.origin[i]);
            d += Math.abs(cube.rotation[i] - snap.rotation[i]) * 0.1;
        }
        d += Math.abs(Number(cube.inflate || 0) - Number(snap.inflate || 0));
        return d;
    }

    function refreshCubeSnapshots() {
        state.cubeSnapshots.clear();
        state.knownCubeUUIDs = new Set();
        if (typeof Cube === 'undefined' || !Cube.all) return;
        for (const cube of Cube.all) {
            state.cubeSnapshots.set(cube.uuid, snapshotCube(cube));
            state.knownCubeUUIDs.add(cube.uuid);
        }
    }

    function getCubeByUUID(uuid) {
        if (!uuid || typeof Cube === 'undefined' || !Cube.all) return null;
        return Cube.all.find(c => c.uuid === uuid) || null;
    }

    function pairCubes(a, b) {
        if (!a || !b || a === b) return;
        state.mirrorPairs.set(a.uuid, b.uuid);
        state.mirrorPairs.set(b.uuid, a.uuid);
        state.mirrorSingles.delete(a.uuid);
        state.mirrorSingles.delete(b.uuid);
    }

    function unpairCube(cubeOrUUID) {
        const uuid = typeof cubeOrUUID === 'string' ? cubeOrUUID : (cubeOrUUID && cubeOrUUID.uuid);
        if (!uuid) return;
        const partnerUUID = state.mirrorPairs.get(uuid);
        state.mirrorPairs.delete(uuid);
        if (partnerUUID) state.mirrorPairs.delete(partnerUUID);
    }

    function cubeParentKey(cube) {
        const parent = cube && cube.parent;
        if (!parent || parent === 'root') return 'root';
        return parent.uuid || String(parent);
    }

    function transformLookupKey(data, rotationAxis, parentKey) {
        const q = value => Math.round(Number(value || 0) * 100000);
        return [
            ...(data.from || []).map(q),
            ...(data.to || []).map(q),
            ...(data.origin || []).map(q),
            ...(data.rotation || []).map(q),
            rotationAxis || '',
            parentKey || 'root',
        ].join('|');
    }

    function cubeTransformLookupKey(cube) {
        return transformLookupKey(cube, cube && cube.rotation_axis, cubeParentKey(cube));
    }

    function mirroredTransformLookupKey(cube) {
        const mirrored = mirroredTransformData(cube);
        return transformLookupKey(mirrored, cube && cube.rotation_axis, cubeParentKey(cube));
    }

    function buildMirrorCandidateIndex(cubes) {
        const index = new Map();
        for (const cube of cubes || []) {
            const key = cubeTransformLookupKey(cube);
            if (!index.has(key)) index.set(key, []);
            index.get(key).push(cube);
        }
        return index;
    }

    function mirroredCubeMatches(source, candidate, axis = state.mirrorAxis, plane = state.mirrorPlane) {
        if (!source || !candidate || source === candidate) return false;
        if (cubeParentKey(source) !== cubeParentKey(candidate)) return false;
        if ((source.rotation_axis || null) !== (candidate.rotation_axis || null)) return false;
        const m = mirroredTransformData(source, axis, plane);
        return arraysNearlyEqual(m.from, candidate.from, 1e-5) &&
               arraysNearlyEqual(m.to, candidate.to, 1e-5) &&
               arraysNearlyEqual(m.origin, candidate.origin, 1e-5) &&
               arraysNearlyEqual(m.rotation, candidate.rotation, 1e-5);
    }

    function findExistingMirroredCube(source, candidateIndex = null) {
        if (!source || !Cube || !Cube.all) return null;
        const candidates = candidateIndex
            ? (candidateIndex.get(mirroredTransformLookupKey(source)) || [])
            : Cube.all;
        return candidates.find(c => {
            if (c === source) return false;
            const paired = state.mirrorPairs.get(c.uuid);
            if (paired && paired !== source.uuid) return false;
            return mirroredCubeMatches(source, c);
        }) || null;
    }

    function rebuildMirrorPairs() {
        state.mirrorPairs.clear();
        state.mirrorSingles.clear();
        state.mirrorAuthority.clear();
        state.pendingVertexSnapAuthority = null;
        if (typeof Cube === 'undefined' || !Cube.all) {
            refreshCubeSnapshots();
            return;
        }

        const cubes = Cube.all.slice();
        const used = new Set();

        // First recognize cubes that are intentionally one symmetric cube.
        for (const cube of cubes) {
            if (cubeCanBeSingleSymmetricCube(cube) && cubeLocalIntersectsPlane(cube) && cubeIsLocallySymmetric(cube)) {
                state.mirrorSingles.add(cube.uuid);
                used.add(cube.uuid);
            }
        }

        // Then pair the remaining exact mirrored counterparts. A lookup table avoids
        // the old O(n²) comparison loop on large models.
        const candidateIndex = buildMirrorCandidateIndex(cubes.filter(cube => !used.has(cube.uuid)));
        for (const a of cubes) {
            if (used.has(a.uuid)) continue;
            const candidates = candidateIndex.get(mirroredTransformLookupKey(a)) || [];
            for (const b of candidates) {
                if (a === b) continue;
                if (used.has(b.uuid)) continue;
                if (mirroredCubeMatches(a, b)) {
                    pairCubes(a, b);
                    used.add(a.uuid);
                    used.add(b.uuid);
                    break;
                }
            }
        }
        refreshCubeSnapshots();
        log(`Mirror state rebuilt: ${state.mirrorPairs.size / 2} pair(s), ${state.mirrorSingles.size} single symmetric cube(s)`);
    }

    function getMirrorAuthority(cube, axis = state.mirrorAxis) {
        const authority = cube && state.mirrorAuthority.get(cube.uuid);
        if (!authority || authority.axis !== axis || (authority.side !== -1 && authority.side !== 1)) return null;
        return authority;
    }

    function chooseSymmetricDistance(cube, previous, axis = state.mirrorAxis, plane = state.mirrorPlane) {
        const a = cube.from[axis];
        const b = cube.to[axis];
        const da = Math.abs(a - plane);
        const db = Math.abs(b - plane);
        const authority = getMirrorAuthority(cube, axis);

        // When a concrete side was grabbed (especially by Vertex Snap), that side is
        // absolute truth. The opposite side is generated afterwards and may never pull
        // the grabbed side back toward the mirror plane.
        if (authority) {
            const low = Math.min(a, b);
            const high = Math.max(a, b);
            return Math.max(0, authority.side < 0 ? plane - low : high - plane);
        }

        if (nearlyEqual(da, db, 1e-6)) return (da + db) / 2;

        if (previous && previous.from && previous.to) {
            const changedA = Math.abs(a - previous.from[axis]);
            const changedB = Math.abs(b - previous.to[axis]);

            // Whichever side the user actually moved becomes authoritative, including
            // inward moves. This prevents a 7-unit half-width from jumping back to 7.
            if (changedA > changedB + 1e-6) return da;
            if (changedB > changedA + 1e-6) return db;

            // Generic transforms sometimes move both limits equally. If there is no
            // recorded grabbed side, preserve the resulting size around the plane.
            return Math.abs(b - a) / 2;
        }

        if (nearlyEqual(a, plane, 1e-6)) return db;
        if (nearlyEqual(b, plane, 1e-6)) return da;
        return Math.max(da, db);
    }

    function symmetrizeCubeInPlace(cube, previous, axis = state.mirrorAxis, plane = state.mirrorPlane) {
        const authority = getMirrorAuthority(cube, axis);
        if (authority) {
            const low = Math.min(cube.from[axis], cube.to[axis]);
            const high = Math.max(cube.from[axis], cube.to[axis]);
            const touched = authority.side < 0 ? low : high;
            const opposite = mirrorCoordinate(touched, plane);
            cube.from[axis] = Math.min(touched, opposite);
            cube.to[axis] = Math.max(touched, opposite);
        } else {
            const distance = Math.max(0, chooseSymmetricDistance(cube, previous, axis, plane));
            cube.from[axis] = plane - distance;
            cube.to[axis] = plane + distance;
        }
        cube.origin[axis] = plane;
        state.mirrorSingles.add(cube.uuid);
    }

    function applyMirroredTransform(source, target, axis = state.mirrorAxis, plane = state.mirrorPlane) {
        // Copy the source transform first, then let Blockbench perform its own flip.
        // This is more robust than hand-editing rotations and works with whichever
        // Minecraft model format is currently open.
        target.from = source.from.slice();
        target.to = source.to.slice();
        target.origin = source.origin.slice();
        target.rotation = source.rotation.slice();
        if ('rotation_axis' in source && 'rotation_axis' in target) target.rotation_axis = source.rotation_axis;
        if ('inflate' in source && 'inflate' in target) target.inflate = source.inflate;
        if ('stretch' in source && 'stretch' in target && Array.isArray(source.stretch)) target.stretch = source.stretch.slice();
        if ('rescale' in source && 'rescale' in target) target.rescale = source.rescale;
        if ('visibility' in source && 'visibility' in target) target.visibility = source.visibility;
        if ('shade' in source && 'shade' in target) target.shade = source.shade;

        try {
            if (typeof target.flip === 'function') {
                target.flip(axis, plane, true);
                return;
            }
        } catch (e) {
            warn('Blockbench flip failed; using fallback mirror math', e);
        }
        const data = mirroredTransformData(source, axis, plane);
        target.from = data.from.slice();
        target.to = data.to.slice();
        target.origin = data.origin.slice();
        target.rotation = data.rotation.slice();
    }

    function pushAspectElement(data, cube) {
        if (!data || !data.aspects || !cube) return;
        if (!Array.isArray(data.aspects.elements)) data.aspects.elements = [];
        if (!data.aspects.elements.includes(cube)) data.aspects.elements.push(cube);
    }

    function selectDriverFromPair(a, b) {
        const sa = state.cubeSnapshots.get(a.uuid);
        const sb = state.cubeSnapshots.get(b.uuid);
        const da = cubeTransformDelta(a, sa);
        const db = cubeTransformDelta(b, sb);
        return db > da ? b : a;
    }

    function synchronizeSmartMirrorInline(data, forcedUUIDs = []) {
        if (!state.smartMirrorEnabled || state.mirrorGuard || !Project || !Cube || !Cube.all) return;
        state.mirrorGuard = true;

        const selectionBefore = currentSelectionUUIDs ? currentSelectionUUIDs() : [];
        const currentByUUID = new Map(Cube.all.map(c => [c.uuid, c]));
        const currentUUIDs = new Set(currentByUUID.keys());
        const dirtyElements = new Set();
        const removedUUIDs = Array.from(state.knownCubeUUIDs).filter(uuid => !currentUUIDs.has(uuid));
        const changed = [];
        const forced = new Set(forcedUUIDs || []);
        for (const uuid of state.forcedMirrorUUIDs) forced.add(uuid);
        state.forcedMirrorUUIDs.clear();

        try {
            // If one half of a pair is deleted, the other half is deleted in the SAME
            // edit. If both were deleted by the user, there is nothing extra to do.
            for (const removedUUID of removedUUIDs) {
                state.mirrorAuthority.delete(removedUUID);
                const partnerUUID = state.mirrorPairs.get(removedUUID);
                if (!partnerUUID) {
                    state.mirrorSingles.delete(removedUUID);
                    continue;
                }
                const partner = currentByUUID.get(partnerUUID);
                if (partner) {
                    pushAspectElement(data, partner);
                    if (data && data.aspects) data.aspects.outliner = true;
                    try { partner.remove(); } catch (e) { warn('Could not remove mirror partner after deletion', e); }
                    currentByUUID.delete(partnerUUID);
                    currentUUIDs.delete(partnerUUID);
                }
                unpairCube(removedUUID);
            }

            for (const cube of Cube.all.slice()) {
                const snap = state.cubeSnapshots.get(cube.uuid);
                if (!snap || cubeTransformChanged(cube, snap) || forced.has(cube.uuid)) changed.push(cube);
            }

            // Collapse changed pair members to ONE driver so the two sides never fight
            // each other and snap the user's edit back.
            const drivers = [];
            const handled = new Set();
            const changedSet = new Set(changed.map(c => c.uuid));
            for (const cube of changed) {
                if (!cube || handled.has(cube.uuid) || !currentByUUID.has(cube.uuid)) continue;
                const partnerUUID = state.mirrorPairs.get(cube.uuid);
                const partner = partnerUUID ? currentByUUID.get(partnerUUID) : null;
                if (partner && changedSet.has(partner.uuid)) {
                    const driver = selectDriverFromPair(cube, partner);
                    drivers.push(driver);
                    handled.add(cube.uuid);
                    handled.add(partner.uuid);
                } else {
                    drivers.push(cube);
                    handled.add(cube.uuid);
                }
            }

            const candidateIndex = buildMirrorCandidateIndex(Array.from(currentByUUID.values()));

            for (const cube of drivers) {
                if (!cube || !currentByUUID.has(cube.uuid)) continue;
                dirtyElements.add(cube);
                const previous = state.cubeSnapshots.get(cube.uuid);
                let partnerUUID = state.mirrorPairs.get(cube.uuid);
                let partner = partnerUUID ? currentByUUID.get(partnerUUID) : null;

                // Merely touching the mirror plane with one face must stay a two-cube
                // pair. Only a cube that actually crosses the plane may collapse into
                // one symmetric cube. This is essential for mirror-plane vertex snap.
                const canBeOneCube = cubeCanBeSingleSymmetricCube(cube) && cubeLocalCrossesPlane(cube);
                if (canBeOneCube) {
                    pushAspectElement(data, cube);
                    if (partner && partner !== cube) {
                        pushAspectElement(data, partner);
                        if (data && data.aspects) data.aspects.outliner = true;
                        try { partner.remove(); } catch (e) { warn('Could not remove obsolete mirror partner', e); }
                        currentByUUID.delete(partner.uuid);
                        currentUUIDs.delete(partner.uuid);
                    }
                    unpairCube(cube);
                    symmetrizeCubeInPlace(cube, previous);
                    // A grabbed-side authority belongs to exactly one user edit. Once
                    // the opposite side has been generated, forget it so later edits
                    // can establish their own authoritative side.
                    state.mirrorAuthority.delete(cube.uuid);
                    continue;
                }

                state.mirrorSingles.delete(cube.uuid);
                if (!partner) {
                    partner = findExistingMirroredCube(cube, candidateIndex);
                    if (partner) pairCubes(cube, partner);
                }

                if (!partner) {
                    try {
                        if (data && data.aspects) data.aspects.outliner = true;
                        partner = cube.duplicate();
                        if (partner) {
                            applyMirroredTransform(cube, partner);
                            pairCubes(cube, partner);
                            pushAspectElement(data, partner);
                            dirtyElements.add(partner);
                            currentByUUID.set(partner.uuid, partner);
                            currentUUIDs.add(partner.uuid);
                        }
                    } catch (e) {
                        warn('Could not create smart mirror cube', e);
                    }
                } else {
                    pushAspectElement(data, partner);
                    applyMirroredTransform(cube, partner);
                    pairCubes(cube, partner);
                    dirtyElements.add(partner);
                }
                state.mirrorAuthority.delete(cube.uuid);
            }

            try {
                if (dirtyElements.size) Canvas.updateView({
                    elements: Array.from(dirtyElements),
                    element_aspects: {transform: true, geometry: true, uv: false},
                    selection: true
                });
            } catch (_) {
                try { Canvas.updateAll(); } catch (_) {}
            }

            // Duplicating a cube can change Blockbench's selection. Put the user's
            // selection back exactly as it was, including multi-selection.
            if (selectionBefore.length) restoreSelectionByUUIDs(selectionBefore.filter(uuid => getCubeByUUID(uuid)), false);
        } finally {
            refreshCubeSnapshots();
            state.mirrorGuard = false;
        }
    }

    function onInitEditSmartMirror(data) {
        if (!state.smartMirrorEnabled || state.mirrorGuard || !data || !data.aspects) return;
        const elements = Array.isArray(data.aspects.elements) ? data.aspects.elements.slice() : [];
        let touchesCube = false;
        for (const el of elements) {
            if (!el || el.type !== 'cube') continue;
            touchesCube = true;
            const partnerUUID = state.mirrorPairs.get(el.uuid);
            const partner = partnerUUID ? getCubeByUUID(partnerUUID) : null;
            if (partner) pushAspectElement(data, partner);
        }
        // Structural changes are possible whenever a cube crosses/leaves the plane.
        // Capturing the outliner at edit start keeps Smart Mirror in the same Undo step.
        if (touchesCube || data.aspects.outliner) data.aspects.outliner = true;
    }

    function onFinishEditSmartMirror(data) {
        if (!state.smartMirrorEnabled || state.mirrorGuard) return;
        try {
            // Vertex Snap first performs Blockbench's normal edit. Only afterwards do
            // we mirror the opposite side around coordinate 8. The clicked side itself
            // therefore never gets pulled back by Smart Mirror.
            primePendingVertexSnapAuthority(data);
            synchronizeSmartMirrorInline(data || {aspects: {elements: [], outliner: true}});
        } catch (e) {
            warn('Automatic Smart Mirror failed', e);
            refreshCubeSnapshots();
        }
    }

    function scheduleSmartMirrorFallback() {
        if (state.syncScheduled) return;
        state.syncScheduled = true;
        state.syncTimer = setTimeout(() => {
            state.syncScheduled = false;
            state.syncTimer = null;
            if (!state.smartMirrorEnabled || state.mirrorGuard || !state.forcedMirrorUUIDs.size) return;
            const pending = Array.from(state.forcedMirrorUUIDs).map(getCubeByUUID).filter(Boolean);
            if (pending.length) processSmartMirrorCubes(pending, {silent: true});
            else state.forcedMirrorUUIDs.clear();
        }, 0);
    }

    function onAddCubeSmartMirror(data) {
        if (!state.smartMirrorEnabled || state.mirrorGuard || !data || !data.object) return;
        state.forcedMirrorUUIDs.add(data.object.uuid);
        // Normal edits are handled by finish_edit and clear this queue first. The
        // deferred fallback covers imports/scripts that emit add_cube without a normal
        // edit lifecycle, so newly added cubes are never left unmirrored.
        scheduleSmartMirrorFallback();
    }

    function onUndoRedoSmartMirror() {
        setTimeout(() => {
            try { rebuildMirrorPairs(); } catch (e) { warn('Could not rebuild mirror state after undo/redo', e); }
        }, 0);
    }

    function processSmartMirrorCubes(cubes, options = {}) {
        // Manual compatibility action. The actual mode uses the normal Blockbench edit
        // lifecycle; this action forces the selected cubes through the same synchronizer.
        cubes = (cubes || []).filter(c => c && c.type === 'cube');
        if (!cubes.length) {
            if (!options.silent) quick('Keine Cubes ausgewählt');
            return;
        }
        const uuids = cubes.map(c => c.uuid);
        try {
            Undo.initEdit({elements: cubes.slice(), outliner: true});
            const fake = {aspects: {elements: cubes.slice(), outliner: true}, message: 'SMS: Spiegelung anwenden'};
            synchronizeSmartMirrorInline(fake, uuids);
            Undo.finishEdit('SMS: Spiegelung anwenden', fake.aspects);
            if (!options.silent) quick(`${cubes.length} Cube(s) mit Smart Mirror synchronisiert`);
        } catch (e) {
            warn('Manual Smart Mirror failed', e);
            try { Undo.cancelEdit(true); } catch (_) {}
        }
    }

    // --------------------------
    // Advanced Vertex Mode + mirror-side tracking
    // --------------------------

    function updateCubeGeometryNow(cube) {
        if (!cube) return;
        try {
            Canvas.updateView({
                elements: [cube],
                element_aspects: {transform: true, geometry: true, uv: false},
                selection: true,
            });
        } catch (_) {
            try { Canvas.updateAll(); } catch (_) {}
        }
        try { if (cube.mesh) cube.mesh.updateMatrixWorld(true); } catch (_) {}
    }

    function quantizeFeatureNumber(n) {
        return Math.round(Number(n || 0) * 1000000) / 1000000;
    }

    function getCubeFeatureGeometry(cube) {
        if (!cube || !cube.mesh || typeof THREE === 'undefined') {
            return null;
        }
        try { cube.mesh.updateMatrixWorld(true); } catch (_) {}
        const unique = [];
        const byKey = new Map();

        // Blockbench exposes the eight transformed cube corners directly. Prefer this
        // API because it also works when the preview mesh uses indexed or optimized
        // geometry. The mesh-buffer fallback keeps compatibility with older 4.x builds.
        try {
            if (typeof cube.getGlobalVertexPositions === 'function') {
                const positions = cube.getGlobalVertexPositions();
                if (Array.isArray(positions) && positions.length >= 8) {
                    const inverse = cube.mesh.matrixWorld.clone().invert();
                    for (const position of positions) {
                        if (!position || position.length < 3) continue;
                        const world = new THREE.Vector3(Number(position[0]), Number(position[1]), Number(position[2]));
                        if (![world.x, world.y, world.z].every(Number.isFinite)) continue;
                        const local = world.clone().applyMatrix4(inverse);
                        const key = `${quantizeFeatureNumber(local.x)}|${quantizeFeatureNumber(local.y)}|${quantizeFeatureNumber(local.z)}`;
                        if (byKey.has(key)) continue;
                        const vertex = {local, world, signs: [0, 0, 0]};
                        byKey.set(key, vertex);
                        unique.push(vertex);
                    }
                }
            }
        } catch (e) {
            warn('Could not use Blockbench cube corner API', e);
        }

        if (unique.length < 8) {
            unique.length = 0;
            byKey.clear();
            const geometry = cube.mesh.geometry;
            const attr = geometry && geometry.attributes && geometry.attributes.position;
            if (!attr) return null;
            for (let i = 0; i < attr.count; i++) {
                const local = new THREE.Vector3().fromBufferAttribute(attr, i);
                const key = `${quantizeFeatureNumber(local.x)}|${quantizeFeatureNumber(local.y)}|${quantizeFeatureNumber(local.z)}`;
                if (byKey.has(key)) continue;
                const vertex = {local, world: local.clone().applyMatrix4(cube.mesh.matrixWorld), signs: [0, 0, 0]};
                byKey.set(key, vertex);
                unique.push(vertex);
            }
        }
        if (unique.length < 8) return null;

        // A normal Blockbench cube produces 8 unique corner positions. In case a host
        // build exposes extra geometry points, only the extreme corner combinations are
        // relevant for cube edge snapping.
        const min = [Infinity, Infinity, Infinity];
        const max = [-Infinity, -Infinity, -Infinity];
        unique.forEach(v => {
            min[0] = Math.min(min[0], v.local.x); max[0] = Math.max(max[0], v.local.x);
            min[1] = Math.min(min[1], v.local.y); max[1] = Math.max(max[1], v.local.y);
            min[2] = Math.min(min[2], v.local.z); max[2] = Math.max(max[2], v.local.z);
        });
        const corners = unique.filter(v => {
            const vals = [v.local.x, v.local.y, v.local.z];
            return vals.every((value, axis) => nearlyEqual(value, min[axis], 1e-5) || nearlyEqual(value, max[axis], 1e-5));
        });
        const vertices = corners.length >= 8 ? corners : unique.slice(0, 8);
        vertices.forEach((v, index) => {
            v.id = index;
            const vals = [v.local.x, v.local.y, v.local.z];
            v.signs = vals.map((value, axis) => Math.abs(value - min[axis]) <= Math.abs(value - max[axis]) ? -1 : 1);
        });

        const edges = [];
        for (let i = 0; i < vertices.length; i++) {
            for (let j = i + 1; j < vertices.length; j++) {
                const a = vertices[i], b = vertices[j];
                const av = [a.local.x, a.local.y, a.local.z];
                const bv = [b.local.x, b.local.y, b.local.z];
                const differing = [];
                for (let axis = 0; axis < 3; axis++) {
                    if (!nearlyEqual(av[axis], bv[axis], 1e-5)) differing.push(axis);
                }
                if (differing.length !== 1) continue;
                const axis = differing[0];
                const fixedSigns = [null, null, null];
                for (let k = 0; k < 3; k++) if (k !== axis) fixedSigns[k] = a.signs[k];
                edges.push({
                    axis,
                    fixedSigns,
                    a,
                    b,
                    key: `${axis}:${fixedSigns.map(v => v === null ? '*' : v).join(',')}`,
                });
            }
        }
        return {vertices, edges};
    }

    function pointToSegmentDistance(point, a, b) {
        const ab = b.clone().sub(a);
        const len2 = ab.lengthSq();
        if (len2 <= EPS) return point.distanceTo(a);
        const t = Math.max(0, Math.min(1, point.clone().sub(a).dot(ab) / len2));
        return point.distanceTo(a.clone().add(ab.multiplyScalar(t)));
    }

    function raycastCubeFromData(data) {
        if (!data) return null;
        if (data.cube && data.cube.type === 'cube') return data.cube;
        if (data.element && data.element.type === 'cube') return data.element;
        let object = data.intersect && data.intersect.object;
        while (object) {
            const cube = Cube && Cube.all ? Cube.all.find(candidate => candidate && candidate.mesh === object) : null;
            if (cube) return cube;
            object = object.parent;
        }
        return null;
    }

    function vectorFromRaycastValue(value) {
        if (!value || typeof THREE === 'undefined') return null;
        if (typeof value.clone === 'function' && Number.isFinite(value.x) && Number.isFinite(value.y) && Number.isFinite(value.z)) return value.clone();
        if (Array.isArray(value) && value.length >= 3) {
            const vector = new THREE.Vector3(Number(value[0]), Number(value[1]), Number(value[2]));
            return [vector.x, vector.y, vector.z].every(Number.isFinite) ? vector : null;
        }
        if (Number.isFinite(value.x) && Number.isFinite(value.y) && Number.isFinite(value.z)) return new THREE.Vector3(value.x, value.y, value.z);
        return null;
    }

    function getRaycastPoint(data) {
        if (!data) return null;
        const direct = vectorFromRaycastValue(data.intersect && data.intersect.point) || vectorFromRaycastValue(data.vertex);
        if (direct) return direct;
        if (Array.isArray(data.intersects)) {
            for (const intersection of data.intersects) {
                const point = vectorFromRaycastValue(intersection && intersection.point);
                if (point) return point;
            }
        }
        if (Array.isArray(data.vertices) && data.vertices.length === 2) {
            const a = vectorFromRaycastValue(data.vertices[0]);
            const b = vectorFromRaycastValue(data.vertices[1]);
            if (a && b) return a.add(b).multiplyScalar(0.5);
        }
        return null;
    }

    function resolveCubeFeatureHit(data) {
        const cube = raycastCubeFromData(data);
        if (!cube) return null;
        const geometry = getCubeFeatureGeometry(cube);
        if (!geometry) return null;
        const point = getRaycastPoint(data);

        if (data.type === 'vertex') {
            let vertex = null;
            // Buffer-geometry indices do not necessarily match the eight de-duplicated
            // cube corners. The world-space hit point is therefore authoritative.
            if (point) {
                vertex = geometry.vertices.reduce((best, candidate) => !best || candidate.world.distanceTo(point) < best.world.distanceTo(point) ? candidate : best, null);
            }
            if (!vertex && Number.isInteger(data.vertex_index) && geometry.vertices[data.vertex_index]) {
                vertex = geometry.vertices[data.vertex_index];
            }
            if (!vertex) return null;
            return {type: 'vertex', cube, vertex, geometry};
        }

        if (data.type === 'line' || data.type === 'edge' || (Array.isArray(data.vertices) && data.vertices.length === 2)) {
            if (!point) return null;
            let edge = null;
            let bestDistance = Infinity;
            geometry.edges.forEach(candidate => {
                const d = pointToSegmentDistance(point, candidate.a.world, candidate.b.world);
                if (d < bestDistance) { bestDistance = d; edge = candidate; }
            });
            if (!edge) return null;
            return {type: 'edge', cube, edge, geometry};
        }
        return null;
    }

    function findEquivalentCubeEdge(cube, descriptor) {
        const geometry = getCubeFeatureGeometry(cube);
        if (!geometry || !descriptor) return null;
        return geometry.edges.find(edge => {
            if (edge.axis !== descriptor.axis) return false;
            for (let axis = 0; axis < 3; axis++) {
                if (axis === edge.axis) continue;
                if (edge.fixedSigns[axis] !== descriptor.fixedSigns[axis]) return false;
            }
            return true;
        }) || null;
    }

    function cloneEdgeDescriptor(edge) {
        return edge ? {axis: edge.axis, fixedSigns: edge.fixedSigns.slice(), key: edge.key} : null;
    }

    function cloneVertexDescriptor(vertex) {
        return vertex ? {signs: vertex.signs.slice()} : null;
    }

    function findEquivalentCubeVertex(cube, descriptor) {
        const geometry = getCubeFeatureGeometry(cube);
        if (!geometry || !descriptor || !Array.isArray(descriptor.signs)) return null;
        return geometry.vertices.find(vertex => vertex.signs.every((sign, axis) => sign === descriptor.signs[axis])) || null;
    }

    function edgeDescriptorFromVertexPair(first, second) {
        if (!first || !second || !Array.isArray(first.signs) || !Array.isArray(second.signs)) return null;
        const differing = [];
        for (let axis = 0; axis < 3; axis++) {
            if (first.signs[axis] !== second.signs[axis]) differing.push(axis);
        }
        if (differing.length !== 1) return null;
        const axis = differing[0];
        const fixedSigns = [null, null, null];
        for (let i = 0; i < 3; i++) if (i !== axis) fixedSigns[i] = first.signs[i];
        return {axis, fixedSigns, key: `${axis}:${fixedSigns.map(value => value === null ? '*' : value).join(',')}`};
    }

    function featureMirrorSide(feature) {
        if (!feature) return 0;
        const axis = state.mirrorAxis;
        if (feature.type === 'vertex' && feature.vertex && feature.vertex.signs) return feature.vertex.signs[axis] || 0;
        if (feature.type === 'edge' && feature.edge) {
            if (feature.edge.axis === axis) return 0;
            return feature.edge.fixedSigns[axis] || 0;
        }
        return 0;
    }

    function setMirrorAuthority(cube, side) {
        if (!cube || (side !== -1 && side !== 1)) return;
        state.mirrorAuthority.set(cube.uuid, {axis: state.mirrorAxis, side});
    }

    function builtInVertexSnapIsActive() {
        try { return typeof Tool !== 'undefined' && Tool.selected && Tool.selected.id === 'vertex_snap_tool'; } catch (_) { return false; }
    }

    function onCanvasClickTrackBuiltInVertexSnap(data) {
        if (!state.smartMirrorEnabled || !builtInVertexSnapIsActive() || !data || data.type !== 'vertex') return;
        const feature = resolveCubeFeatureHit(data);
        if (!feature || !feature.cube || !state.mirrorSingles.has(feature.cube.uuid)) return;
        if (!Cube.selected || !Cube.selected.includes(feature.cube)) return;
        const side = featureMirrorSide(feature);
        if (side !== -1 && side !== 1) return;
        state.pendingVertexSnapAuthority = {
            uuid: feature.cube.uuid,
            axis: state.mirrorAxis,
            side,
            time: Date.now(),
        };
    }

    function primePendingVertexSnapAuthority(data) {
        const pending = state.pendingVertexSnapAuthority;
        if (!pending) return;
        const age = Date.now() - pending.time;
        const touched = !data || !data.aspects || !Array.isArray(data.aspects.elements) || data.aspects.elements.some(el => el && el.uuid === pending.uuid);
        if (age <= 10000 && touched && pending.axis === state.mirrorAxis) {
            state.mirrorAuthority.set(pending.uuid, {axis: pending.axis, side: pending.side});
        }
        if (touched || age > 10000) state.pendingVertexSnapAuthority = null;
    }

    function nativeVertexSnapAvailable() {
        return typeof Vertexsnap !== 'undefined' && Vertexsnap &&
               typeof Vertexsnap.canvasClick === 'function' &&
               typeof Vertexsnap.select === 'function';
    }

    function refreshNativeVertexSnapGizmos() {
        if (!nativeVertexSnapAvailable()) return;
        try { Vertexsnap.select(); } catch (e) { warn('Could not refresh native Vertex Snap gizmos', e); }
    }

    function resetNativeVertexSnapWorkflow(reselect = false) {
        if (!nativeVertexSnapAvailable()) return;
        try {
            Vertexsnap.step1 = true;
            if (typeof Vertexsnap.clearVertexGizmos === 'function') Vertexsnap.clearVertexGizmos();
            if (reselect) Vertexsnap.select();
        } catch (e) {
            warn('Could not reset native Vertex Snap workflow', e);
        }
    }

    function handleNativeVertexSnapInsideAdvancedMode(data, hit) {
        if (!nativeVertexSnapAvailable() || !hit || hit.type !== 'vertex') return false;

        // On the first click, keep Blockbench's normal rule: the source vertex belongs
        // to the currently selected source element. We then delegate the complete
        // Move/Scale/Rotate behavior to Blockbench's own Vertex Snap implementation.
        if (Vertexsnap.step1 !== false) {
            const selected = Cube.selected ? Cube.selected.filter(c => c && c.type === 'cube') : [];
            if (!selected.includes(hit.cube)) {
                quick('Die erste Ecke muss zum ausgewählten Quell-Cube gehören');
                return true;
            }

            // Remember which side of a one-piece Smart-Mirror cube the user actually
            // grabbed. The native snap runs first. Smart Mirror only constructs the
            // opposite side after Undo.finishEdit, so the touched side stays exact.
            if (state.smartMirrorEnabled && state.mirrorSingles.has(hit.cube.uuid)) {
                const side = featureMirrorSide(hit);
                if (side === -1 || side === 1) {
                    state.pendingVertexSnapAuthority = {
                        uuid: hit.cube.uuid,
                        axis: state.mirrorAxis,
                        side,
                        time: Date.now(),
                    };
                }
            }
        }

        try {
            Vertexsnap.canvasClick(data);
            // After a completed native snap, stay ready for either another normal
            // corner snap or a new edge workflow without changing tools.
            if (Vertexsnap.step1 !== false) {
                resetAdvancedVertexOperation(true);
                refreshNativeVertexSnapGizmos();
            }
            return true;
        } catch (e) {
            warn('Native Vertex Snap delegation failed', e);
            resetNativeVertexSnapWorkflow(true);
            quick('Normales Vertex Snap konnte nicht ausgeführt werden');
            return true;
        }
    }

    function advancedSourceCube() {
        let cube = getCubeByUUID(state.advancedVertex.sourceCubeUUID);
        if (cube) return cube;
        const selected = Cube && Cube.selected ? Cube.selected.filter(c => c && c.type === 'cube') : [];
        cube = selected.length ? selected[selected.length - 1] : null;
        if (cube) state.advancedVertex.sourceCubeUUID = cube.uuid;
        return cube;
    }

    function resetAdvancedVertexOperation(keepSource = true) {
        if (!keepSource) state.advancedVertex.sourceCubeUUID = null;
        state.advancedVertex.sourceVertex = null;
        state.advancedVertex.sourceEdge = null;
        state.advancedVertex.sourceEdgeVertexA = null;
        state.advancedVertex.targetVertexA = null;
        state.advancedVertex.stage = 'source_feature';
    }

    function worldLengthOfEdge(edge) {
        return edge && edge.a && edge.b ? edge.a.world.distanceTo(edge.b.world) : 0;
    }

    function setCubeAxisToWorldLength(cube, edgeDescriptor, desiredWorldLength) {
        const edge = findEquivalentCubeEdge(cube, edgeDescriptor);
        if (!edge || !Number.isFinite(desiredWorldLength) || desiredWorldLength <= EPS) return false;
        const axis = edge.axis;
        const currentWorldLength = worldLengthOfEdge(edge);
        const rawSize = Math.abs(cube.to[axis] - cube.from[axis]);
        const inflate = Number(cube.inflate || 0);
        const visibleRawSize = Math.max(EPS, rawSize + inflate * 2);
        const worldPerRawUnit = currentWorldLength / visibleRawSize;
        if (!Number.isFinite(worldPerRawUnit) || worldPerRawUnit <= EPS) return false;
        const newRawSize = Math.max(0, desiredWorldLength / worldPerRawUnit - inflate * 2);
        const center = (cube.from[axis] + cube.to[axis]) / 2;
        cube.from[axis] = center - newRawSize / 2;
        cube.to[axis] = center + newRawSize / 2;
        return true;
    }

    function translateCubeWorld(cube, fromWorld, toWorld) {
        if (!cube || !cube.mesh || !fromWorld || !toWorld) return false;
        try { cube.mesh.updateMatrixWorld(true); } catch (_) {}
        const parent = cube.mesh.parent;
        if (!parent || typeof parent.worldToLocal !== 'function') return false;
        try { parent.updateMatrixWorld(true); } catch (_) {}
        const a = parent.worldToLocal(fromWorld.clone());
        const b = parent.worldToLocal(toWorld.clone());
        const delta = b.sub(a);
        if (![delta.x, delta.y, delta.z].every(Number.isFinite)) return false;
        for (let axis = 0; axis < 3; axis++) {
            const d = [delta.x, delta.y, delta.z][axis];
            cube.from[axis] += d;
            cube.to[axis] += d;
            cube.origin[axis] += d;
        }
        return true;
    }

    function moveSourceVertexToTarget(sourceCube, sourceDescriptor, targetVertex) {
        if (!sourceCube || !sourceDescriptor || !targetVertex || !targetVertex.world) return false;
        const sourceVertex = findEquivalentCubeVertex(sourceCube, sourceDescriptor);
        if (!sourceVertex) {
            quick('Die gewählte Quellecke existiert nicht mehr');
            return false;
        }
        try {
            Undo.initEdit({elements: [sourceCube], outliner: !!state.smartMirrorEnabled});
            if (!translateCubeWorld(sourceCube, sourceVertex.world, targetVertex.world)) throw new Error('Could not translate source corner');
            updateCubeGeometryNow(sourceCube);
            Undo.finishEdit('SMS: Ecke auf Ecke verschieben', {elements: [sourceCube], outliner: !!state.smartMirrorEnabled});
            return true;
        } catch (e) {
            warn('Smart corner snap failed', e);
            try { Undo.cancelEdit(true); } catch (_) {}
            quick('Die Ecke konnte nicht verschoben werden');
            return false;
        }
    }

    function moveSourceVertexToMirrorPlane(sourceCube, sourceDescriptor) {
        if (!state.smartMirrorEnabled) {
            quick('Dafür muss die SMS-Spiegelmodellierung aktiv sein');
            return false;
        }
        const sourceVertex = findEquivalentCubeVertex(sourceCube, sourceDescriptor);
        if (!sourceVertex || !sourceCube.mesh || !sourceCube.mesh.parent) {
            quick('Die gewählte Ecke konnte nicht bestimmt werden');
            return false;
        }
        try {
            sourceCube.mesh.parent.updateMatrixWorld(true);
            const localVertex = sourceCube.mesh.parent.worldToLocal(sourceVertex.world.clone());
            const coordinate = [localVertex.x, localVertex.y, localVertex.z][state.mirrorAxis];
            const delta = state.mirrorPlane - coordinate;
            if (!Number.isFinite(delta)) throw new Error('Invalid mirror-axis offset');

            Undo.initEdit({elements: [sourceCube], outliner: true});
            sourceCube.from[state.mirrorAxis] += delta;
            sourceCube.to[state.mirrorAxis] += delta;
            sourceCube.origin[state.mirrorAxis] += delta;
            updateCubeGeometryNow(sourceCube);
            Undo.finishEdit('SMS: Ecke an Spiegelachse ausrichten', {elements: [sourceCube], outliner: true});
            quick(`Cube nur auf ${axisName()} verschoben · Gegenstück symmetrisch aktualisiert`, 3600);
            return true;
        } catch (e) {
            warn('Mirror-plane corner snap failed', e);
            try { Undo.cancelEdit(true); } catch (_) {}
            quick('Die Ecke konnte nicht an der Spiegelachse ausgerichtet werden');
            return false;
        }
    }

    function rotateCubeWorldDirection(cube, sourceDirection, targetDirection) {
        if (!cube || !cube.mesh || !sourceDirection || !targetDirection || sourceDirection.lengthSq() <= EPS || targetDirection.lengthSq() <= EPS) return false;
        try { cube.mesh.updateMatrixWorld(true); } catch (_) {}
        const src = sourceDirection.clone().normalize();
        const dst = targetDirection.clone().normalize();
        const delta = new THREE.Quaternion().setFromUnitVectors(src, dst);
        const currentWorld = new THREE.Quaternion();
        cube.mesh.getWorldQuaternion(currentWorld);
        const desiredWorld = delta.clone().multiply(currentWorld);

        const parentWorld = new THREE.Quaternion();
        if (cube.mesh.parent && typeof cube.mesh.parent.getWorldQuaternion === 'function') cube.mesh.parent.getWorldQuaternion(parentWorld);
        const local = parentWorld.clone().invert().multiply(desiredWorld);
        const order = cube.mesh.rotation && cube.mesh.rotation.order ? cube.mesh.rotation.order : 'XYZ';
        const euler = new THREE.Euler().setFromQuaternion(local, order);
        const radToDeg = 180 / Math.PI;
        cube.rotation[0] = euler.x * radToDeg;
        cube.rotation[1] = euler.y * radToDeg;
        cube.rotation[2] = euler.z * radToDeg;
        return true;
    }

    function matchSourceEdgeLengthToTarget(sourceCube, sourceDescriptor, targetEdge) {
        const targetLength = worldLengthOfEdge(targetEdge);
        if (targetLength <= EPS) {
            quick('Die Zielkante hat keine nutzbare Länge');
            return false;
        }
        try {
            Undo.initEdit({elements: [sourceCube]});
            if (!setCubeAxisToWorldLength(sourceCube, sourceDescriptor, targetLength)) throw new Error('Source edge could not be resized');
            const sourceFeature = {type: 'edge', edge: findEquivalentCubeEdge(sourceCube, sourceDescriptor)};
            const side = featureMirrorSide(sourceFeature);
            if (state.smartMirrorEnabled && state.mirrorSingles.has(sourceCube.uuid)) setMirrorAuthority(sourceCube, side);
            updateCubeGeometryNow(sourceCube);
            Undo.finishEdit('SMS: Kantenlänge übernehmen');
            return true;
        } catch (e) {
            warn('Advanced edge length match failed', e);
            try { Undo.cancelEdit(true); } catch (_) {}
            quick('Kantenlänge konnte nicht übernommen werden');
            return false;
        }
    }

    function fitSourceEdgeBetweenVertices(sourceCube, sourceDescriptor, targetA, targetB) {
        if (!targetA || !targetB || !targetA.world || !targetB.world) return false;
        const desiredA = targetA.world.clone();
        const desiredB = targetB.world.clone();
        const desiredLength = desiredA.distanceTo(desiredB);
        if (desiredLength <= EPS) {
            quick('Die beiden Zielecken liegen am gleichen Punkt');
            return false;
        }
        try {
            Undo.initEdit({elements: [sourceCube]});
            const originalEdge = findEquivalentCubeEdge(sourceCube, sourceDescriptor);
            if (!originalEdge) throw new Error('Source edge vanished');
            const side = featureMirrorSide({type: 'edge', edge: originalEdge});

            if (!setCubeAxisToWorldLength(sourceCube, sourceDescriptor, desiredLength)) throw new Error('Could not resize source edge');
            updateCubeGeometryNow(sourceCube);

            let edge = findEquivalentCubeEdge(sourceCube, sourceDescriptor);
            if (!edge) throw new Error('Could not resolve resized source edge');
            let currentA = edge.a.world.clone();
            let currentB = edge.b.world.clone();
            const sourceDirection = currentB.clone().sub(currentA);
            let targetDirection = desiredB.clone().sub(desiredA);

            // Pick the endpoint ordering that requires the smaller turn.
            if (sourceDirection.dot(targetDirection) < 0) {
                const tmp = desiredA.clone();
                desiredA.copy(desiredB);
                desiredB.copy(tmp);
                targetDirection = desiredB.clone().sub(desiredA);
            }

            if (!rotateCubeWorldDirection(sourceCube, sourceDirection, targetDirection)) throw new Error('Could not rotate source cube');
            updateCubeGeometryNow(sourceCube);

            edge = findEquivalentCubeEdge(sourceCube, sourceDescriptor);
            if (!edge) throw new Error('Could not resolve rotated source edge');
            const currentMid = edge.a.world.clone().add(edge.b.world).multiplyScalar(0.5);
            const targetMid = desiredA.clone().add(desiredB).multiplyScalar(0.5);
            if (!translateCubeWorld(sourceCube, currentMid, targetMid)) throw new Error('Could not translate source cube');
            if (state.smartMirrorEnabled && state.mirrorSingles.has(sourceCube.uuid)) setMirrorAuthority(sourceCube, side);
            updateCubeGeometryNow(sourceCube);

            // One tiny midpoint correction compensates for host-side rounding or pivot
            // updates that may happen when the cube transform is refreshed.
            edge = findEquivalentCubeEdge(sourceCube, sourceDescriptor);
            if (edge) {
                const correctedMid = edge.a.world.clone().add(edge.b.world).multiplyScalar(0.5);
                const wantedMid = desiredA.clone().add(desiredB).multiplyScalar(0.5);
                if (correctedMid.distanceTo(wantedMid) > 1e-6) {
                    translateCubeWorld(sourceCube, correctedMid, wantedMid);
                    updateCubeGeometryNow(sourceCube);
                }
            }

            Undo.finishEdit('SMS: Kante zwischen Ecken einpassen');
            return true;
        } catch (e) {
            warn('Advanced edge bridge failed', e);
            try { Undo.cancelEdit(true); } catch (_) {}
            quick('Kante konnte nicht zwischen den Ecken eingepasst werden');
            return false;
        }
    }

    function handleAdvancedVertexClick(data) {
        const hit = resolveCubeFeatureHit(data);
        if (!hit) {
            quick('Keine Ecke oder Kante erkannt · näher an einen Griffpunkt klicken');
            return;
        }
        let sourceCube = advancedSourceCube();
        const event = data && data.event;
        const shiftPressed = !!(event && event.shiftKey);
        const altPressed = !!(event && event.altKey);

        if (!sourceCube) {
            if (hit.cube) {
                selectOnlyCubes([hit.cube]);
                state.advancedVertex.sourceCubeUUID = hit.cube.uuid;
                resetAdvancedVertexOperation(true);
                quick('Quell-Cube gewählt · jetzt Ecke oder Kante anklicken');
            }
            return;
        }

        if (state.advancedVertex.stage === 'source_feature') {
            if (hit.type === 'vertex') {
                if (hit.cube !== sourceCube) {
                    quick('Die erste Ecke muss zum ausgewählten Quell-Cube gehören');
                    return;
                }
                if (shiftPressed) {
                    state.advancedVertex.sourceEdgeVertexA = cloneVertexDescriptor(hit.vertex);
                    state.advancedVertex.stage = 'source_edge_second_vertex';
                    quick('Erster Kantenpunkt gewählt · mit Umschalt die benachbarte Ecke anklicken', 3600);
                    return;
                }
                const descriptor = cloneVertexDescriptor(hit.vertex);
                if (altPressed) {
                    if (moveSourceVertexToMirrorPlane(sourceCube, descriptor)) {
                        resetAdvancedVertexOperation(true);
                        refreshNativeVertexSnapGizmos();
                    }
                    return;
                }
                state.advancedVertex.sourceVertex = descriptor;
                state.advancedVertex.stage = 'target_vertex';
                quick(state.smartMirrorEnabled
                    ? 'Quellecke gewählt · jetzt Zielecke anklicken · Alt+Klick auf die Quellecke richtet sie direkt an der Spiegelachse aus'
                    : 'Quellecke gewählt · jetzt eine Zielecke anklicken', 5200);
                return;
            }
            if (hit.type !== 'edge') {
                quick('Eine Quellecke oder Quellkante anklicken');
                return;
            }
            if (hit.cube !== sourceCube) {
                quick('Die erste Kante muss zum ausgewählten Quell-Cube gehören');
                return;
            }
            // If a half-finished native vertex operation existed, choosing an edge is
            // an explicit switch to the edge workflow. Cancel only that pending snap.
            resetNativeVertexSnapWorkflow(false);
            state.pendingVertexSnapAuthority = null;
            state.advancedVertex.sourceEdge = cloneEdgeDescriptor(hit.edge);
            state.advancedVertex.stage = 'target_choice';
            quick('Quellkante gewählt - jetzt Zielkante ODER erste Zielecke anklicken', 3600);
            return;
        }

        if (state.advancedVertex.stage === 'source_edge_second_vertex') {
            if (hit.type !== 'vertex' || hit.cube !== sourceCube) {
                quick('Bitte eine benachbarte zweite Ecke desselben Quell-Cubes anklicken');
                return;
            }
            const descriptor = edgeDescriptorFromVertexPair(state.advancedVertex.sourceEdgeVertexA, hit.vertex);
            if (!descriptor) {
                quick('Diese beiden Ecken bilden keine direkte Cube-Kante');
                return;
            }
            state.advancedVertex.sourceEdge = descriptor;
            state.advancedVertex.sourceEdgeVertexA = null;
            state.advancedVertex.stage = 'target_choice';
            quick('Quellkante über zwei Ecken gewählt · jetzt Zielkante oder erste Zielecke anklicken', 4200);
            return;
        }

        if (state.advancedVertex.stage === 'target_vertex') {
            if (altPressed && state.advancedVertex.sourceVertex) {
                if (moveSourceVertexToMirrorPlane(sourceCube, state.advancedVertex.sourceVertex)) {
                    resetAdvancedVertexOperation(true);
                    refreshNativeVertexSnapGizmos();
                }
                return;
            }
            if (hit.type !== 'vertex') {
                quick('Als Ziel bitte eine Ecke anklicken');
                return;
            }
            if (hit.cube === sourceCube) {
                quick('Die Zielecke muss zu einem anderen Cube gehören');
                return;
            }
            if (moveSourceVertexToTarget(sourceCube, state.advancedVertex.sourceVertex, hit.vertex)) {
                resetAdvancedVertexOperation(true);
                refreshNativeVertexSnapGizmos();
                quick('Quellecke auf Zielecke verschoben · Größe und Rotation unverändert');
            }
            return;
        }

        if (state.advancedVertex.stage === 'target_choice') {
            if (hit.type === 'edge') {
                if (hit.cube === sourceCube) {
                    quick('Die Zielkante muss zu einem anderen Cube gehören');
                    return;
                }
                if (matchSourceEdgeLengthToTarget(sourceCube, state.advancedVertex.sourceEdge, hit.edge)) {
                    resetAdvancedVertexOperation(true);
                    quick('Kantenlänge übernommen - nächste Quellkante wählen');
                }
                return;
            }
            if (hit.type === 'vertex') {
                state.advancedVertex.targetVertexA = {
                    cubeUUID: hit.cube.uuid,
                    world: hit.vertex.world.clone(),
                    signs: hit.vertex.signs.slice(),
                };
                state.advancedVertex.stage = 'second_vertex';
                quick('Erste Zielecke gewählt - jetzt zweite Zielecke anklicken');
                return;
            }
        }

        if (state.advancedVertex.stage === 'second_vertex') {
            if (hit.type !== 'vertex') {
                quick('Als zweiten Zielpunkt bitte eine Ecke anklicken');
                return;
            }
            const targetB = {
                cubeUUID: hit.cube.uuid,
                world: hit.vertex.world.clone(),
                signs: hit.vertex.signs.slice(),
            };
            if (fitSourceEdgeBetweenVertices(sourceCube, state.advancedVertex.sourceEdge, state.advancedVertex.targetVertexA, targetB)) {
                resetAdvancedVertexOperation(true);
                refreshNativeVertexSnapGizmos();
                quick('Kante exakt zwischen den beiden Ecken eingepasst');
            }
        }
    }

    // --------------------------
    // Duplicate checker
    // --------------------------

    function exactCubeSignature(cube) {
        // Exact from/to plus pivot and rotation: no rounding and no tolerance.
        return JSON.stringify({
            from: cube.from,
            to: cube.to,
            origin: cube.origin,
            rotation: cube.rotation,
            rotation_axis: cube.rotation_axis || null,
        });
    }

    function findExactDuplicateGroups() {
        const map = new Map();
        for (const cube of Cube.all) {
            const key = exactCubeSignature(cube);
            if (!map.has(key)) map.set(key, []);
            map.get(key).push(cube);
        }
        return Array.from(map.values()).filter(group => group.length > 1);
    }

    function setCubeMarkerColorRaw(cube, color) {
        try {
            cube.color = color;
            if (cube.updateElement) cube.updateElement();
        } catch (e) {
            warn('Could not set marker color', e);
        }
    }

    function markElementSelected(el) {
        if (!el) return;
        try {
            // Blockbench 5.x
            if (typeof el.markAsSelected === 'function') {
                el.markAsSelected();
                return;
            }
            // Blockbench 4.x compatibility (renamed to markAsSelected in 5.0)
            if (typeof el.selectLow === 'function') {
                el.selectLow();
                return;
            }
            // Last-resort fallback: emulate additive selection.
            if (typeof el.select === 'function') {
                el.select({shiftKey: true, ctrlKey: true, metaKey: true});
            }
        } catch (e) {
            warn('Could not mark element selected', e);
        }
    }

    function selectOnlyElements(elements) {
        elements = (elements || []).filter(Boolean);
        state.selectionGuard = true;
        try {
            if (typeof unselectAll === 'function') unselectAll();
            else {
                for (const el of (Outliner.selected || []).slice()) {
                    try { el.unselect(); } catch (_) {}
                }
            }
            elements.forEach(markElementSelected);
            try {
                if (typeof updateSelection === 'function') updateSelection();
                else Blockbench.dispatchEvent('update_selection', {});
            } catch (_) {}
            try { Canvas.updateView({elements, selection: true}); } catch (_) {}
        } finally {
            state.selectionGuard = false;
        }
    }

    function selectOnlyCubes(cubes) {
        selectOnlyElements(cubes);
    }

    function closeDuplicateReview(restoreColors = true) {
        const review = state.duplicateReview;
        if (review && restoreColors) {
            for (const cube of review.cubes) {
                if (cube && Cube.all.includes(cube) && review.oldColors.has(cube.uuid)) {
                    setCubeMarkerColorRaw(cube, review.oldColors.get(cube.uuid));
                }
            }
            try { Canvas.updateView({elements: review.cubes.filter(c => Cube.all.includes(c)), selection: true}); } catch (_) {}
        }
        state.duplicateReview = null;
        if (state.duplicateReviewNode) {
            try { state.duplicateReviewNode.remove(); } catch (_) {}
            state.duplicateReviewNode = null;
        }
    }

    function createDuplicateReviewCard(groups, duplicates, selectionBefore) {
        closeDuplicateReview(false);
        const oldColors = new Map(duplicates.map(c => [c.uuid, c.color]));
        state.duplicateReview = {groups, cubes: duplicates, oldColors, selectionBefore: (selectionBefore || []).slice()};

        const card = document.createElement('div');
        card.id = 'sms_duplicate_review';
        card.innerHTML = `
            <div class="sms_dup_title">Exakte Duplikate markiert</div>
            <div class="sms_dup_text">${groups.length} Gruppe(n), ${duplicates.length} Cube(s). Du kannst das Modell jetzt frei drehen und prüfen.</div>
            <div class="sms_dup_buttons">
                <button class="sms_dup_delete">Duplikate löschen</button>
                <button class="sms_dup_keep">Behalten</button>
                <button class="sms_dup_cancel">Abbrechen</button>
            </div>
        `;
        document.body.appendChild(card);
        state.duplicateReviewNode = card;

        card.querySelector('.sms_dup_delete').addEventListener('click', () => resolveDuplicateReview('delete'));
        card.querySelector('.sms_dup_keep').addEventListener('click', () => resolveDuplicateReview('keep'));
        card.querySelector('.sms_dup_cancel').addEventListener('click', () => resolveDuplicateReview('cancel'));
    }

    function resolveDuplicateReview(action) {
        const review = state.duplicateReview;
        if (!review) return;
        const groups = review.groups;
        const oldColors = review.oldColors;
        const all = review.cubes.slice();

        // Remove the floating card first, but restore original marker colors before any
        // permanent edit is created.
        if (state.duplicateReviewNode) {
            try { state.duplicateReviewNode.remove(); } catch (_) {}
            state.duplicateReviewNode = null;
        }
        for (const cube of all) {
            if (cube && Cube.all.includes(cube) && oldColors.has(cube.uuid)) setCubeMarkerColorRaw(cube, oldColors.get(cube.uuid));
        }
        state.duplicateReview = null;

        if (action === 'cancel') {
            selectOnlyElements((review.selectionBefore || []).map(findOutlinerElementByUUID).filter(Boolean));
            state.currentSelection = currentSelectionUUIDs();
            try { Canvas.updateView({elements: all.filter(c => Cube.all.includes(c)), selection: true}); } catch (_) {}
            quick('Duplikatprüfung abgebrochen');
            return;
        }

        if (action !== 'delete') {
            selectOnlyCubes(all.filter(c => Cube.all.includes(c)));
            state.previousSelection = (review.selectionBefore || []).slice();
            state.currentSelection = currentSelectionUUIDs();
            try { Canvas.updateView({elements: all.filter(c => Cube.all.includes(c)), selection: true}); } catch (_) {}
            quick('Duplikate beibehalten');
            return;
        }

        const toDelete = [];
        const keep = [];
        groups.forEach(group => {
            const existing = group.filter(c => Cube.all.includes(c));
            if (!existing.length) return;
            keep.push(existing[0]);
            toDelete.push(...existing.slice(1));
        });
        if (!toDelete.length) {
            quick('Keine Duplikate mehr vorhanden');
            return;
        }

        try {
            Undo.initEdit({elements: [...keep, ...toDelete], outliner: true});
            toDelete.forEach(c => {
                try { c.remove(); } catch (e) { warn('Could not delete duplicate', e); }
            });
            Undo.finishEdit('Exakte Cube-Duplikate löschen', {elements: keep.filter(c => Cube.all.includes(c)), outliner: true});
        } catch (e) {
            warn('Duplicate delete failed', e);
            try { Undo.cancelEdit(true); } catch (_) {}
        }
        selectOnlyCubes(keep.filter(c => Cube.all.includes(c)));
        state.previousSelection = (review.selectionBefore || []).slice();
        state.currentSelection = currentSelectionUUIDs();
        quick(`${toDelete.length} exakte Duplikate gelöscht`);
    }

    function checkForDuplicates() {
        closeDuplicateReview(true);
        const selectionBefore = currentSelectionUUIDs();
        const groups = findExactDuplicateGroups();
        if (!groups.length) {
            quick('Keine exakten Cube-Duplikate gefunden');
            return;
        }

        const duplicates = groups.flat();
        const oldColors = new Map(duplicates.map(c => [c.uuid, c.color]));
        duplicates.forEach(c => setCubeMarkerColorRaw(c, 3));
        selectOnlyCubes(duplicates);
        try { Canvas.updateView({elements: duplicates, element_aspects: {geometry: true}, selection: true}); } catch (_) {}

        createDuplicateReviewCard(groups, duplicates, selectionBefore);
        // createDuplicateReviewCard makes its own old-color snapshot after the cubes were
        // marked red, so replace it with the true pre-scan colors here.
        if (state.duplicateReview) state.duplicateReview.oldColors = oldColors;
        quick('Duplikate rot markiert - Modell prüfen, dann rechts unten entscheiden', 4200);
    }

    // --------------------------
    // Selection history / sticky selection
    // --------------------------

    function currentSelectionUUIDs() {
        if (!Outliner || !Outliner.selected) return [];
        return Outliner.selected.filter(el => el && el.uuid).map(el => el.uuid);
    }

    function sameUUIDSelection(a, b) {
        if (a.length !== b.length) return false;
        const set = new Set(a);
        return set.size === a.length && b.every(uuid => set.has(uuid));
    }

    function findOutlinerElementByUUID(uuid) {
        if (!uuid) return null;
        if (Cube && Cube.all) {
            const cube = Cube.all.find(c => c.uuid === uuid);
            if (cube) return cube;
        }
        try {
            if (Outliner && Outliner.elements) {
                const el = Outliner.elements.find(e => e.uuid === uuid);
                if (el) return el;
            }
        } catch (_) {}
        try {
            if (typeof Group !== 'undefined' && Group.all) {
                const g = Group.all.find(e => e.uuid === uuid);
                if (g) return g;
            }
        } catch (_) {}
        return null;
    }

    function restoreSelectionByUUIDs(uuids, message) {
        const seen = new Set();
        const elements = uuids.map(findOutlinerElementByUUID).filter(el => {
            if (!el || seen.has(el.uuid)) return false;
            seen.add(el.uuid);
            return true;
        });
        if (!elements.length) {
            if (message) quick('Die gespeicherte Auswahl existiert nicht mehr');
            return false;
        }
        selectOnlyElements(elements);
        state.currentSelection = elements.map(el => el.uuid);
        if (message) quick(`${elements.length} Element(e) wieder ausgewählt`);
        return true;
    }

    function onSelectionUpdate() {
        if (state.selectionGuard) return;
        const now = currentSelectionUUIDs();

        if (state.stickySelection && now.length === 0 && !state.allowExplicitClear && state.stickySelectionSnapshot.length) {
            state.selectionGuard = true;
            setTimeout(() => {
                try {
                    restoreSelectionByUUIDs(state.stickySelectionSnapshot, false);
                } finally {
                    state.selectionGuard = false;
                }
            }, 0);
            return;
        }

        if (now.length > 0) {
            if (state.currentSelection.length && !sameUUIDSelection(now, state.currentSelection)) {
                state.previousSelection = state.currentSelection.slice();
            }
            state.currentSelection = now.slice();
            if (state.stickySelection) state.stickySelectionSnapshot = now.slice();
        } else if (state.currentSelection.length) {
            state.previousSelection = state.currentSelection.slice();
            state.currentSelection = [];
        }

        // While waiting for a new source edge, an explicit selection in the outliner or
        // viewport should immediately become the Advanced Vertex source cube.
        try {
            if (typeof Tool !== 'undefined' && Tool.selected && Tool.selected.id === 'sms_advanced_vertex_mode' && state.advancedVertex.stage === 'source_feature') {
                const selectedCubes = Cube.selected ? Cube.selected.filter(c => c && c.type === 'cube') : [];
                if (selectedCubes.length) state.advancedVertex.sourceCubeUUID = selectedCubes[selectedCubes.length - 1].uuid;
                if (!nativeVertexSnapAvailable() || Vertexsnap.step1 !== false) refreshNativeVertexSnapGizmos();
            }
        } catch (_) {}
    }

    function restorePreviousSelection() {
        if (!state.previousSelection.length) {
            quick('Keine vorherige Auswahl gespeichert');
            return;
        }
        const oldCurrent = state.currentSelection.slice();
        if (restoreSelectionByUUIDs(state.previousSelection, true)) {
            state.previousSelection = oldCurrent;
            if (state.stickySelection) state.stickySelectionSnapshot = state.currentSelection.slice();
        }
    }

    function explicitClearSelection() {
        state.allowExplicitClear = true;
        state.selectionGuard = true;
        try {
            const now = currentSelectionUUIDs();
            if (now.length) {
                state.previousSelection = now.slice();
                state.currentSelection = [];
            }
            if (typeof unselectAll === 'function') unselectAll();
            else {
                for (const el of (Outliner.selected || []).slice()) {
                    try { el.unselect(); } catch (_) {}
                }
            }
            state.stickySelectionSnapshot = [];
            try { Canvas.updateView({selection: true}); } catch (_) {}
        } finally {
            state.selectionGuard = false;
            setTimeout(() => { state.allowExplicitClear = false; }, 0);
        }
        quick('Auswahl explizit aufgehoben');
    }

    // --------------------------
    // Texture optimizer
    // --------------------------

    function getSelectedTexture() {
        if (Texture && Texture.selected) return Texture.selected;
        if (Project && Project.selected_texture) return Project.selected_texture;
        if (Texture && Texture.all && Texture.all.length === 1) return Texture.all[0];
        if (Texture && Texture.getDefault) {
            try { return Texture.getDefault(); } catch (_) {}
        }
        return null;
    }

    function pixelAligned(value, eps = 1e-5) {
        return Math.abs(value - Math.round(value)) <= eps;
    }

    function facePixelRect(face, texture) {
        const uv = face.uv;
        if (!uv || uv.length < 4) return null;
        const uvW = texture.getUVWidth ? texture.getUVWidth() : (texture.uv_width || Project.texture_width || texture.width);
        const uvH = texture.getUVHeight ? texture.getUVHeight() : (texture.uv_height || Project.texture_height || texture.height);
        if (!uvW || !uvH || !texture.width || !texture.height) return null;

        const px = [
            uv[0] / uvW * texture.width,
            uv[1] / uvH * texture.height,
            uv[2] / uvW * texture.width,
            uv[3] / uvH * texture.height,
        ];

        if (!px.every(pixelAligned)) return {unaligned: true};
        const x1 = Math.round(px[0]);
        const y1 = Math.round(px[1]);
        const x2 = Math.round(px[2]);
        const y2 = Math.round(px[3]);
        const x = Math.min(x1, x2);
        const y = Math.min(y1, y2);
        const w = Math.abs(x2 - x1);
        const h = Math.abs(y2 - y1);
        if (w < 1 || h < 1) return null;
        if (x < 0 || y < 0 || x + w > texture.width || y + h > texture.height) return {outOfBounds: true};
        return {x, y, w, h, flipU: x1 > x2, flipV: y1 > y2, uvW, uvH};
    }

    function rgbaEqualAt(data, width, x1, y1, x2, y2) {
        let i1 = (y1 * width + x1) * 4;
        let i2 = (y2 * width + x2) * 4;
        return data[i1] === data[i2] && data[i1+1] === data[i2+1] && data[i1+2] === data[i2+2] && data[i1+3] === data[i2+3];
    }

    function divisors(n) {
        const low = [];
        const high = [];
        for (let i = 1; i * i <= n; i++) {
            if (n % i !== 0) continue;
            low.push(i);
            if (i * i !== n) high.unshift(n / i);
        }
        return low.concat(high);
    }

    function reducePatchLosslessly(imageData) {
        const {width: w, height: h, data} = imageData;
        const candidates = [];
        for (const rw of divisors(w)) {
            for (const rh of divisors(h)) {
                if (rw === w && rh === h) continue;
                candidates.push({rw, rh, area: rw * rh});
            }
        }
        candidates.sort((a, b) => a.area - b.area || Math.max(a.rw, a.rh) - Math.max(b.rw, b.rh));

        for (const {rw, rh} of candidates) {
            const sx = w / rw;
            const sy = h / rh;
            let ok = true;

            outer:
            for (let ry = 0; ry < rh; ry++) {
                for (let rx = 0; rx < rw; rx++) {
                    const baseX = rx * sx;
                    const baseY = ry * sy;
                    for (let yy = 0; yy < sy; yy++) {
                        for (let xx = 0; xx < sx; xx++) {
                            if (!rgbaEqualAt(data, w, baseX, baseY, baseX + xx, baseY + yy)) {
                                ok = false;
                                break outer;
                            }
                        }
                    }
                }
            }
            if (!ok) continue;

            const reduced = new Uint8ClampedArray(rw * rh * 4);
            for (let ry = 0; ry < rh; ry++) {
                for (let rx = 0; rx < rw; rx++) {
                    const src = ((ry * sy) * w + (rx * sx)) * 4;
                    const dst = (ry * rw + rx) * 4;
                    reduced[dst] = data[src];
                    reduced[dst+1] = data[src+1];
                    reduced[dst+2] = data[src+2];
                    reduced[dst+3] = data[src+3];
                }
            }
            return {w: rw, h: rh, pixels: reduced};
        }
        return {w, h, pixels: new Uint8ClampedArray(data)};
    }

    function fnv1a32(bytes, w, h) {
        let hash = 0x811c9dc5;
        hash ^= w; hash = Math.imul(hash, 0x01000193);
        hash ^= h; hash = Math.imul(hash, 0x01000193);
        for (let i = 0; i < bytes.length; i++) {
            hash ^= bytes[i];
            hash = Math.imul(hash, 0x01000193);
        }
        return (hash >>> 0).toString(16);
    }

    function pixelArraysEqual(a, b) {
        if (a.length !== b.length) return false;
        for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
        return true;
    }

    function createImageDataFromPixels(pixels, w, h) {
        try {
            return new ImageData(new Uint8ClampedArray(pixels), w, h);
        } catch (_) {
            const canvas = document.createElement('canvas');
            const ctx = canvas.getContext('2d');
            const id = ctx.createImageData(w, h);
            id.data.set(pixels);
            return id;
        }
    }

    function cubeUsesTexture(cube, texture) {
        if (!cube || !cube.faces) return false;
        for (const key in cube.faces) {
            const face = cube.faces[key];
            if (face && face.getTexture && face.getTexture() === texture) return true;
        }
        return false;
    }

    function cubesUsingTexture(texture) {
        return (Cube && Cube.all ? Cube.all : []).filter(cube => cubeUsesTexture(cube, texture));
    }

    function boxUVCubesUsingTexture(texture) {
        return cubesUsingTexture(texture).filter(cube => !!cube.box_uv);
    }

    function collectTexturePatches(texture) {
        const ctx = texture.ctx || (texture.canvas && texture.canvas.getContext('2d'));
        if (!ctx) throw new Error('Textur-Canvas nicht verfügbar');

        const buckets = new Map();
        const reductionCache = new Map();
        const uniquePatches = [];
        const refs = [];
        let skippedBoxUV = 0;
        let skippedUnaligned = 0;
        let skippedOutOfBounds = 0;

        for (const cube of Cube.all) {
            if (cube.box_uv) {
                // Box UV is implicit; direct face UV edits would not be reliable.
                let usesTexture = false;
                for (const key in cube.faces) {
                    const f = cube.faces[key];
                    if (f && f.getTexture && f.getTexture() === texture) { usesTexture = true; break; }
                }
                if (usesTexture) skippedBoxUV++;
                continue;
            }

            for (const key in cube.faces) {
                const face = cube.faces[key];
                if (!face || face.enabled === false || !face.getTexture || face.getTexture() !== texture) continue;
                const rect = facePixelRect(face, texture);
                if (!rect) continue;
                if (rect.unaligned) { skippedUnaligned++; continue; }
                if (rect.outOfBounds) { skippedOutOfBounds++; continue; }

                const rectKey = `${rect.x}|${rect.y}|${rect.w}|${rect.h}`;
                let reduced = reductionCache.get(rectKey);
                if (!reduced) {
                    const image = ctx.getImageData(rect.x, rect.y, rect.w, rect.h);
                    reduced = reducePatchLosslessly(image);
                    reductionCache.set(rectKey, reduced);
                }
                const hash = fnv1a32(reduced.pixels, reduced.w, reduced.h);

                let patch = null;
                const candidates = buckets.get(hash) || [];
                for (const candidate of candidates) {
                    if (candidate.w === reduced.w && candidate.h === reduced.h && pixelArraysEqual(candidate.pixels, reduced.pixels)) {
                        patch = candidate;
                        break;
                    }
                }

                if (!patch) {
                    patch = {
                        id: uniquePatches.length,
                        w: reduced.w,
                        h: reduced.h,
                        pixels: reduced.pixels,
                        refs: [],
                        x: 0,
                        y: 0,
                    };
                    uniquePatches.push(patch);
                    candidates.push(patch);
                    buckets.set(hash, candidates);
                }

                const ref = {cube, face, faceKey: key, rect, patch};
                patch.refs.push(ref);
                refs.push(ref);
            }
        }

        return {uniquePatches, refs, skippedBoxUV, skippedUnaligned, skippedOutOfBounds};
    }

    function rectContains(a, b) {
        return b.x >= a.x && b.y >= a.y && b.x + b.w <= a.x + a.w && b.y + b.h <= a.y + a.h;
    }

    function pruneFreeRects(free) {
        for (let i = 0; i < free.length; i++) {
            for (let j = i + 1; j < free.length; j++) {
                if (rectContains(free[i], free[j])) {
                    free.splice(j, 1); j--;
                } else if (rectContains(free[j], free[i])) {
                    free.splice(i, 1); i--; break;
                }
            }
        }
    }

    function splitFreeRect(freeRect, usedRect) {
        const out = [];
        const fx2 = freeRect.x + freeRect.w;
        const fy2 = freeRect.y + freeRect.h;
        const ux2 = usedRect.x + usedRect.w;
        const uy2 = usedRect.y + usedRect.h;

        if (usedRect.x >= fx2 || ux2 <= freeRect.x || usedRect.y >= fy2 || uy2 <= freeRect.y) {
            return [freeRect];
        }
        if (usedRect.x > freeRect.x) out.push({x: freeRect.x, y: freeRect.y, w: usedRect.x - freeRect.x, h: freeRect.h});
        if (ux2 < fx2) out.push({x: ux2, y: freeRect.y, w: fx2 - ux2, h: freeRect.h});
        if (usedRect.y > freeRect.y) out.push({x: freeRect.x, y: freeRect.y, w: freeRect.w, h: usedRect.y - freeRect.y});
        if (uy2 < fy2) out.push({x: freeRect.x, y: uy2, w: freeRect.w, h: fy2 - uy2});
        return out.filter(r => r.w > 0 && r.h > 0);
    }

    function maxRectsPack(patches, size, padding) {
        const items = patches.slice().sort((a, b) => {
            const aMax = Math.max(a.w, a.h), bMax = Math.max(b.w, b.h);
            if (bMax !== aMax) return bMax - aMax;
            return (b.w * b.h) - (a.w * a.h);
        });

        let free = [{x: 0, y: 0, w: size, h: size}];
        const placements = new Map();

        for (const patch of items) {
            const pw = patch.w + padding * 2;
            const ph = patch.h + padding * 2;
            let bestIndex = -1;
            let bestScore1 = Infinity;
            let bestScore2 = Infinity;

            for (let i = 0; i < free.length; i++) {
                const r = free[i];
                if (pw <= r.w && ph <= r.h) {
                    const leftoverH = r.h - ph;
                    const leftoverW = r.w - pw;
                    const shortSide = Math.min(leftoverH, leftoverW);
                    const longSide = Math.max(leftoverH, leftoverW);
                    if (shortSide < bestScore1 || (shortSide === bestScore1 && longSide < bestScore2)) {
                        bestIndex = i;
                        bestScore1 = shortSide;
                        bestScore2 = longSide;
                    }
                }
            }

            if (bestIndex < 0) return null;
            const chosen = free[bestIndex];
            const used = {x: chosen.x, y: chosen.y, w: pw, h: ph};
            placements.set(patch.id, {x: used.x + padding, y: used.y + padding});

            const newFree = [];
            for (const r of free) newFree.push(...splitFreeRect(r, used));
            free = newFree;
            pruneFreeRects(free);
        }

        return placements;
    }

    function nextPowerOfTwo(n) {
        let p = 1;
        while (p < n) p <<= 1;
        return p;
    }

    function findSmallestSquarePacking(patches, padding, maxSize) {
        let minDim = 1;
        let area = 0;
        for (const p of patches) {
            minDim = Math.max(minDim, p.w + padding * 2, p.h + padding * 2);
            area += (p.w + padding * 2) * (p.h + padding * 2);
        }
        let size = nextPowerOfTwo(Math.max(minDim, Math.ceil(Math.sqrt(area))));
        size = Math.max(1, size);
        while (size <= maxSize) {
            const placements = maxRectsPack(patches, size, padding);
            if (placements) return {size, placements};
            size *= 2;
        }
        return null;
    }

    function buildOptimizedTexture(texture, collected, packing, padding) {
        const {size, placements} = packing;
        const canvas = document.createElement('canvas');
        canvas.width = size;
        canvas.height = size;
        const ctx = canvas.getContext('2d');
        ctx.clearRect(0, 0, size, size);
        ctx.imageSmoothingEnabled = false;

        for (const patch of collected.uniquePatches) {
            const pos = placements.get(patch.id);
            patch.x = pos.x;
            patch.y = pos.y;
            const id = createImageDataFromPixels(patch.pixels, patch.w, patch.h);
            ctx.putImageData(id, patch.x, patch.y);
        }
        return canvas;
    }

    function applyOptimizedUVs(texture, collected, newSize) {
        const affectedCubes = new Set();
        for (const ref of collected.refs) {
            const {face, rect, patch, cube} = ref;
            affectedCubes.add(cube);
            const uMin = patch.x / newSize * rect.uvW;
            const vMin = patch.y / newSize * rect.uvH;
            const uMax = (patch.x + patch.w) / newSize * rect.uvW;
            const vMax = (patch.y + patch.h) / newSize * rect.uvH;
            face.uv[0] = rect.flipU ? uMax : uMin;
            face.uv[2] = rect.flipU ? uMin : uMax;
            face.uv[1] = rect.flipV ? vMax : vMin;
            face.uv[3] = rect.flipV ? vMin : vMax;
        }
        return Array.from(affectedCubes);
    }

    function optimizeSelectedTexture() {
        const texture = getSelectedTexture();
        if (!texture) {
            quick('Keine Textur ausgewählt');
            return;
        }
        if (texture.frameCount && texture.frameCount > 1) {
            Blockbench.showMessageBox({
                title: 'Texture Optimizer',
                icon: 'warning',
                message: 'Animierte Texturen werden aktuell nicht verändert, damit keine Frames zerstört werden.',
                buttons: ['OK']
            });
            return;
        }
        if (texture.layers_enabled && texture.layers && texture.layers.length) {
            Blockbench.showMessageBox({
                title: 'Texture Optimizer',
                icon: 'warning',
                message: 'Texturen mit aktiven Ebenen werden nicht verändert, damit keine Ebenen oder Bearbeitungsdaten verloren gehen.',
                buttons: ['OK']
            });
            return;
        }
        if (!texture.canvas || !texture.width || !texture.height) {
            quick('Textur ist noch nicht vollständig geladen');
            return;
        }

        const affectedBefore = cubesUsingTexture(texture);
        const boxUVBefore = affectedBefore.filter(cube => !!cube.box_uv);
        let editOpen = false;
        let collected;

        try {
            // Box UV was the reason the first build reported "no optimizable per-face
            // surfaces". Convert those cubes losslessly to per-face UV INSIDE the same
            // Undo step, then pack them exactly like all other faces.
            Undo.initEdit({
                elements: affectedBefore.slice(),
                textures: [texture],
                bitmap: true,
                uv_mode: true,
            });
            editOpen = true;

            for (const cube of boxUVBefore) {
                if (typeof cube.setUVMode === 'function') cube.setUVMode(false);
                else cube.box_uv = false;
            }

            collected = collectTexturePatches(texture);
            if (collected.skippedBoxUV || collected.skippedUnaligned || collected.skippedOutOfBounds) {
                try { Undo.cancelEdit(true); } catch (_) {}
                editOpen = false;
                const reasons = [];
                if (collected.skippedBoxUV) reasons.push(`${collected.skippedBoxUV} nicht konvertierte Box-UV-Cube(s)`);
                if (collected.skippedUnaligned) reasons.push(`${collected.skippedUnaligned} nicht pixelgenaue UV-Fläche(n)`);
                if (collected.skippedOutOfBounds) reasons.push(`${collected.skippedOutOfBounds} UV-Fläche(n) außerhalb der Textur`);
                Blockbench.showMessageBox({
                    title: 'Texture Optimizer',
                    icon: 'warning',
                    message: `Die Textur wurde unverändert gelassen. Für eine garantiert verlustfreie Optimierung müssen zuerst folgende Stellen korrigiert werden: ${reasons.join(', ')}.`,
                    buttons: ['OK']
                });
                return;
            }
            if (!collected.refs.length) {
                try { Undo.cancelEdit(true); } catch (_) {}
                editOpen = false;
                quick('Keine verwendeten UV-Flächen für diese Textur gefunden');
                return;
            }

            const padding = 1;
            const originalWidth = texture.width;
            const originalHeight = texture.height;
            const originalMax = Math.max(originalWidth, originalHeight);
            const hardMax = Math.max(4096, nextPowerOfTwo(originalMax));
            const packing = findSmallestSquarePacking(collected.uniquePatches, padding, hardMax);
            if (!packing) {
                try { Undo.cancelEdit(true); } catch (_) {}
                editOpen = false;
                quick('Kein gültiges Texture-Packing gefunden');
                return;
            }

            const optimizedCanvas = buildOptimizedTexture(texture, collected, packing, padding);
            const affectedCubes = applyOptimizedUVs(texture, collected, packing.size);
            const dataURL = optimizedCanvas.toDataURL('image/png');

            if (texture.updateSource) texture.updateSource(dataURL);
            else if (texture.fromDataURL) texture.fromDataURL(dataURL);
            if (texture.convertToInternal) texture.convertToInternal(dataURL);

            texture.width = packing.size;
            texture.height = packing.size;
            texture.keep_size = true;
            if (texture.canvas) {
                texture.canvas.width = packing.size;
                texture.canvas.height = packing.size;
                const tctx = texture.canvas.getContext('2d');
                tctx.clearRect(0, 0, packing.size, packing.size);
                tctx.imageSmoothingEnabled = false;
                tctx.drawImage(optimizedCanvas, 0, 0);
            }
            if (texture.updateImageFromCanvas) texture.updateImageFromCanvas();
            if (texture.updateChangesAfterEdit) texture.updateChangesAfterEdit();
            else if (texture.updateMaterial) texture.updateMaterial();

            try {
                Canvas.updateView({elements: affectedCubes, element_aspects: {uv: true, geometry: false}, selection: true});
            } catch (_) {
                try { Canvas.updateAll(); } catch (_) {}
            }

            Undo.finishEdit('Texture logisch optimieren', {
                elements: affectedCubes,
                textures: [texture],
                bitmap: true,
                uv_mode: true,
            });
            editOpen = false;

            const total = collected.refs.length;
            const unique = collected.uniquePatches.length;
            const reused = total - unique;
            const boxInfo = boxUVBefore.length ? ` · ${boxUVBefore.length} Box-UV-Cube(s) in per-face UV übernommen` : '';
            quick(`Textur optimiert: ${originalWidth} x ${originalHeight}px -> ${packing.size} x ${packing.size}px · ${reused} Bereich(e) wiederverwendet${boxInfo}`, 5200);
        } catch (e) {
            warn('Texture optimizer failed', e);
            if (editOpen) {
                try { Undo.cancelEdit(true); } catch (_) {}
            }
            quick('Texturoptimierung fehlgeschlagen - Änderung wurde zurückgesetzt', 4200);
        }
    }

    // --------------------------
    // Detailed blade generator
    // --------------------------

    function clampNumber(value, min, max) {
        return Math.max(min, Math.min(max, Number(value)));
    }

    function analyzeBladeSelection(cubes) {
        cubes = (cubes || []).filter(cube => cube && cube.type === 'cube');
        if (cubes.length < 2 || cubes.length % 2 !== 0) {
            return {error: 'Für die Klinge muss eine gerade Anzahl von mindestens zwei Cubes ausgewählt sein.'};
        }
        const parent = cubes[0].parent || 'root';
        if (cubes.some(cube => (cube.parent || 'root') !== parent)) {
            return {error: 'Alle ausgewählten Klingen-Cubes müssen in derselben Gruppe liegen.'};
        }

        const min = [Infinity, Infinity, Infinity];
        const max = [-Infinity, -Infinity, -Infinity];
        for (const cube of cubes) {
            for (let axis = 0; axis < 3; axis++) {
                min[axis] = Math.min(min[axis], cube.from[axis], cube.to[axis]);
                max[axis] = Math.max(max[axis], cube.from[axis], cube.to[axis]);
            }
        }
        const spans = min.map((value, axis) => Math.max(0, max[axis] - value));
        let depthAxis = 0;
        for (let axis = 1; axis < 3; axis++) {
            if (spans[axis] < spans[depthAxis]) depthAxis = axis;
        }
        const inPlaneAxes = [0, 1, 2].filter(axis => axis !== depthAxis);
        const center = min.map((value, axis) => (value + max[axis]) / 2);
        const currentThickness = spans[depthAxis];
        const referenceThickness = currentThickness > 1e-5 ? currentThickness : 1;
        return {cubes, parent, min, max, spans, center, depthAxis, inPlaneAxes, currentThickness, referenceThickness};
    }

    function bladeLayerScale(layerFraction, sharpnessPercent) {
        const sharpness = clampNumber(sharpnessPercent, 0, 100) / 100;
        const maximumInset = 0.04 + 0.26 * sharpness;
        const exponent = 2.8 - 2.0 * sharpness;
        const inset = maximumInset * Math.pow(clampNumber(layerFraction, 0, 1), exponent);
        return Math.max(0.2, 1 - inset);
    }

    function applyBladeLayerTransform(cube, source, analysis, layerCenter, slabThickness, scale) {
        const depthAxis = analysis.depthAxis;
        for (let axis = 0; axis < 3; axis++) {
            if (axis === depthAxis) continue;
            const pivot = analysis.center[axis];
            cube.from[axis] = pivot + (source.from[axis] - pivot) * scale;
            cube.to[axis] = pivot + (source.to[axis] - pivot) * scale;
            cube.origin[axis] = pivot + (source.origin[axis] - pivot) * scale;
        }

        const sourceDepthCenter = (source.from[depthAxis] + source.to[depthAxis]) / 2;
        cube.from[depthAxis] = layerCenter - slabThickness / 2;
        cube.to[depthAxis] = layerCenter + slabThickness / 2;
        cube.origin[depthAxis] = source.origin[depthAxis] + (layerCenter - sourceDepthCenter);
    }

    function createDetailedBlade(analysis, options) {
        const layersPerSide = Math.round(clampNumber(options.layersPerSide, 1, 16));
        const finalThickness = clampNumber(options.finalThickness, 0.01, 128);
        const sharpness = clampNumber(options.sharpness, 0, 100);
        const totalLayerCount = layersPerSide * 2 + 1;
        const createdCount = analysis.cubes.length * layersPerSide * 2;
        if (createdCount > 2400) {
            quick(`Abgebrochen: ${createdCount} neue Cubes wären zu viel · weniger Layer oder Cubes wählen`, 5200);
            return false;
        }

        const slabThickness = finalThickness / totalLayerCount;
        const sources = analysis.cubes.map(cube => ({
            cube,
            from: cube.from.slice(),
            to: cube.to.slice(),
            origin: cube.origin.slice(),
            name: cube.name || 'Cube',
        }));
        const created = [];
        let editOpen = false;
        const oldMirrorGuard = state.mirrorGuard;

        try {
            state.mirrorGuard = true;
            Undo.initEdit({elements: analysis.cubes.slice(), outliner: true});
            editOpen = true;

            // The existing profile becomes the exact middle layer. Every new layer is
            // placed at the same distance on both sides, so the result cannot drift.
            for (const source of sources) {
                applyBladeLayerTransform(source.cube, source, analysis, analysis.center[analysis.depthAxis], slabThickness, 1);
                updateCubeGeometryNow(source.cube);
            }

            for (let layer = 1; layer <= layersPerSide; layer++) {
                const fraction = layer / layersPerSide;
                const scale = bladeLayerScale(fraction, sharpness);
                for (const side of [-1, 1]) {
                    const layerCenter = analysis.center[analysis.depthAxis] + side * layer * slabThickness;
                    for (const source of sources) {
                        const copy = source.cube.duplicate();
                        if (!copy || copy.type !== 'cube') throw new Error('Cube duplication failed');
                        copy.name = `${source.name}_Klinge_${side < 0 ? 'L' : 'R'}${layer}`;
                        try {
                            const uniqueName = copy.createUniqueName && copy.createUniqueName();
                            if (uniqueName) copy.name = uniqueName;
                        } catch (_) {}
                        applyBladeLayerTransform(copy, source, analysis, layerCenter, slabThickness, scale);
                        updateCubeGeometryNow(copy);
                        created.push(copy);
                    }
                }
            }

            const allAffected = analysis.cubes.concat(created);
            Undo.finishEdit('SMS: Detaillierte Klinge erzeugen', {elements: allAffected, outliner: true});
            editOpen = false;
            state.mirrorGuard = oldMirrorGuard;

            selectOnlyCubes(allAffected);
            try {
                Canvas.updateView({
                    elements: allAffected,
                    element_aspects: {transform: true, geometry: true, uv: true},
                    selection: true,
                });
            } catch (_) {
                try { Canvas.updateAll(); } catch (_) {}
            }
            if (state.smartMirrorEnabled) rebuildMirrorPairs();
            quick(`${created.length} Klingen-Cubes erzeugt · ${totalLayerCount} Schichten · ${finalThickness.toFixed(3)} Cube-Einheiten dick`, 5600);
            return true;
        } catch (e) {
            warn('Detailed blade generation failed', e);
            state.mirrorGuard = oldMirrorGuard;
            if (editOpen) {
                try { Undo.cancelEdit(true); } catch (_) {}
            }
            quick('Die detaillierte Klinge konnte nicht erzeugt werden · Änderung zurückgesetzt', 5200);
            return false;
        }
    }

    function openDetailedBladeDialog() {
        const selected = Cube && Cube.selected ? Cube.selected.filter(cube => cube && cube.type === 'cube') : [];
        const analysis = analyzeBladeSelection(selected);
        if (analysis.error) {
            quick(analysis.error, 5200);
            return;
        }

        const defaultUnits = Math.max(0.25, analysis.currentThickness > 1e-5 ? analysis.currentThickness * 2 : 2);
        let lastUnits = Math.round(defaultUnits * 1000) / 1000;
        let lastPercent = Math.round((lastUnits / analysis.referenceThickness) * 1000) / 10;
        let syncing = false;
        let dialog = null;
        dialog = new Dialog({
            id: 'smart_modeling_detailed_blade',
            title: 'SMS: Detaillierte Klinge erzeugen',
            form: {
                selection_info: {
                    label: 'Erkannte Ausgangsform',
                    type: 'info',
                    text: `${analysis.cubes.length} Cubes · Tiefenachse ${axisName(analysis.depthAxis)} · aktuelle Dicke ${analysis.currentThickness.toFixed(3)}`
                },
                final_thickness_units: {
                    label: 'Enddicke in Cube-Einheiten',
                    type: 'number',
                    value: lastUnits,
                    min: 0.01,
                    max: 128,
                    step: 0.05,
                },
                final_thickness_percent: {
                    label: 'Enddicke in % der Ausgangsdicke',
                    type: 'number',
                    value: lastPercent,
                    min: 0.1,
                    max: 100000,
                    step: 1,
                },
                percent_info: {
                    label: 'Prozent-Bezug',
                    type: 'info',
                    text: analysis.currentThickness > 1e-5
                        ? `100 % = ${analysis.referenceThickness.toFixed(3)} Cube-Einheiten Ausgangsdicke.`
                        : 'Das Ausgangsprofil ist 0 dick; deshalb entsprechen hier 100 % genau 1 Cube-Einheit.'
                },
                sharpness: {
                    label: 'Klingenschärfe / äußere Steilheit (%)',
                    type: 'number',
                    value: 65,
                    min: 0,
                    max: 100,
                    step: 1,
                },
                layers_per_side: {
                    label: 'Zusätzliche Cube-Layer je Seite',
                    type: 'number',
                    value: 4,
                    min: 1,
                    max: 16,
                    step: 1,
                },
                layer_info: {
                    label: 'Layer-Ergebnis',
                    type: 'info',
                    text: 'Bei 4 Layern je Seite entstehen 8 neue Layer plus die vorhandene Mittelschicht.'
                },
            },
            onFormChange(result) {
                if (syncing || !dialog) return;
                const units = Number(result.final_thickness_units);
                const percent = Number(result.final_thickness_percent);
                const unitsChanged = Number.isFinite(units) && Math.abs(units - lastUnits) > 1e-8;
                const percentChanged = Number.isFinite(percent) && Math.abs(percent - lastPercent) > 1e-8;
                syncing = true;
                if (unitsChanged && !percentChanged) {
                    lastUnits = clampNumber(units, 0.01, 128);
                    lastPercent = Math.round((lastUnits / analysis.referenceThickness) * 1000) / 10;
                    dialog.setFormValues({final_thickness_percent: lastPercent}, false);
                } else if (percentChanged) {
                    lastPercent = clampNumber(percent, 0.1, 100000);
                    lastUnits = Math.round((analysis.referenceThickness * lastPercent / 100) * 1000) / 1000;
                    dialog.setFormValues({final_thickness_units: lastUnits}, false);
                }
                syncing = false;
            },
            onConfirm(result) {
                createDetailedBlade(analysis, {
                    finalThickness: Number(result.final_thickness_units),
                    sharpness: Number(result.sharpness),
                    layersPerSide: Number(result.layers_per_side),
                });
            }
        });
        dialog.show();
    }

    // --------------------------
    // UI / Actions
    // --------------------------

    function openMirrorSettings() {
        new Dialog({
            id: 'smart_modeling_mirror_settings',
            title: 'SMS: Spiegelmodellierung – Einstellungen',
            form: {
                axis: {
                    label: 'Spiegelachse',
                    type: 'select',
                    value: axisName(),
                    options: {X: 'X / YZ-Ebene', Y: 'Y / XZ-Ebene', Z: 'Z / XY-Ebene'}
                },
                center_info: {
                    label: 'Spiegelebene',
                    type: 'info',
                    text: 'Fest auf Koordinate 8 - also exakt in der Mitte eines 0 bis 16 Minecraft-Modells.'
                },
            },
            onConfirm(result) {
                state.mirrorAxis = result.axis === 'Y' ? 1 : result.axis === 'Z' ? 2 : 0;
                state.mirrorPlane = 8;
                rebuildMirrorPairs();
                quick(`SMS-Spiegelachse: ${axisName()} = 8`);
            }
        }).show();
    }

    function addAction(action, toolbar = true) {
        actions.push(action);
        try { MenuBar.addAction(action, 'tools'); } catch (e) { warn('Could not add menu action', e); }
        if (toolbar) {
            try { if (Toolbars && Toolbars.tools) Toolbars.tools.add(action); } catch (e) { /* toolbar may not exist in older builds */ }
        }
    }

    function installCSS() {
        if (!Blockbench.addCSS) return;
        state.cssHandle = Blockbench.addCSS(`
            #sms_duplicate_review {
                position: fixed;
                right: 24px;
                bottom: 24px;
                z-index: 100000;
                width: min(360px, calc(100vw - 48px));
                padding: 14px;
                border-radius: 8px;
                background: var(--color-back, #202225);
                color: var(--color-text, #f2f2f2);
                border: 1px solid var(--color-border, #555);
                box-shadow: 0 8px 28px rgba(0,0,0,.42);
                font-family: inherit;
                pointer-events: auto;
            }
            #sms_duplicate_review .sms_dup_title {
                font-weight: 700;
                margin-bottom: 7px;
            }
            #sms_duplicate_review .sms_dup_text {
                line-height: 1.35;
                opacity: .95;
                margin-bottom: 12px;
            }
            #sms_duplicate_review .sms_dup_buttons {
                display: flex;
                flex-wrap: wrap;
                gap: 8px;
                justify-content: flex-end;
            }
            #sms_duplicate_review button {
                padding: 6px 10px;
                cursor: pointer;
            }
        `);
    }

    Plugin.register(PLUGIN_ID, {
        title: 'Smart Modeling Suite',
        author: 'ayfer51',
        description: 'Deutsche Modellierwerkzeuge: intelligente Spiegelmodellierung, Eck- und Kantensnapping, detaillierte Klingen, Duplikatprüfung und verlustfreie Texturoptimierung.',
        icon: 'construction',
        version: VERSION,
        variant: 'both',
        min_version: '4.9.0',
        repository: 'https://github.com/ayfer51/ayfer51-blockbench-modeling',
        website: 'https://github.com/ayfer51/ayfer51-blockbench-modeling',

        onload() {
            log(`Loading v${VERSION}`);
            installCSS();

            const smartMirrorToggle = new Toggle('sms_smart_mirror_modeling', {
                name: 'SMS: Intelligente Spiegelmodellierung',
                description: 'Kontinuierlicher Mirror-Modeling-Modus bei Koordinate 8. Neue Cubes, Größenänderungen, Bewegung, Rotation, Löschen und Vertex Snap werden automatisch gespiegelt; die angefasste Seite bleibt dabei unverändert.',
                icon: 'compare_arrows',
                value: false,
                onChange(value) {
                    state.smartMirrorEnabled = !!value;
                    state.mirrorPlane = 8;
                    if (value) {
                        rebuildMirrorPairs();
                        try { disableNativeMirrorForProject(); } catch (_) {}
                        // Existing selected cubes become active Smart-Mirror drivers on
                        // their next edit; all newly created cubes are handled immediately
                        // by the normal Blockbench edit lifecycle.
                        quick(`SMS-Spiegelmodellierung AN · ${axisName()} = 8`);
                    } else {
                        restoreNativeMirrorStates();
                        refreshCubeSnapshots();
                        quick('SMS-Spiegelmodellierung AUS');
                    }
                }
            });
            addAction(smartMirrorToggle);

            addAction(new Action('sms_mirror_settings', {
                name: 'SMS: Spiegelachse festlegen',
                description: 'X, Y oder Z wählen. Die Spiegelebene liegt immer bei Koordinate 8.',
                icon: 'settings',
                click: openMirrorSettings
            }), false);

            const advancedVertexTool = new Tool('sms_advanced_vertex_mode', {
                name: 'SMS: Intelligentes Eck-/Kanten-Snapping',
                description: 'Ecke auf Ecke verschieben, mit Alt eine Ecke an der Spiegelachse ausrichten oder Kanten direkt beziehungsweise mit Umschalt + zwei benachbarten Ecken wählen.',
                icon: 'icon-vertexsnap',
                category: 'tools',
                modes: ['edit'],
                transformerMode: 'hidden',
                toolbar: 'vertex_snap',
                selectElements: false,
                click_locked_elements: false,
                raycast_options: {edges: true, vertices: true},
                condition: () => !!Project && typeof Cube !== 'undefined' && Cube.all && Cube.all.length > 0,
                onSelect() {
                    resetAdvancedVertexOperation(false);
                    resetNativeVertexSnapWorkflow(false);
                    const selected = Cube.selected ? Cube.selected.filter(c => c && c.type === 'cube') : [];
                    if (selected.length) state.advancedVertex.sourceCubeUUID = selected[selected.length - 1].uuid;
                    refreshNativeVertexSnapGizmos();
                    quick(state.advancedVertex.sourceCubeUUID
                        ? 'SMS-Snapping: Ecke oder Kante wählen · Alt = Spiegelachse · Umschalt + 2 Ecken = Kante'
                        : 'SMS-Snapping: zuerst einen Quell-Cube auswählen', 5200);
                },
                onCanvasClick(data) {
                    handleAdvancedVertexClick(data);
                },
                onCanvasRightClick() {
                    resetAdvancedVertexOperation(true);
                    state.pendingVertexSnapAuthority = null;
                    resetNativeVertexSnapWorkflow(true);
                    quick('SMS-Snapping zurückgesetzt · Ecke oder Quellkante wählen');
                    return false;
                },
                onUnselect() {
                    resetAdvancedVertexOperation(false);
                    state.pendingVertexSnapAuthority = null;
                    resetNativeVertexSnapWorkflow(false);
                }
            });
            addAction(advancedVertexTool);

            addAction(new Action('sms_check_duplicates', {
                name: 'SMS: Exakte Duplikate prüfen',
                description: 'Findet nur Cubes mit exakt identischem from/to, Pivot und Rotation. Treffer bleiben im frei drehbaren Modell rot markiert.',
                icon: 'content_copy',
                condition: () => !!Project && Cube.all && Cube.all.length > 1,
                click: checkForDuplicates
            }));

            addAction(new Action('sms_optimize_texture', {
                name: 'SMS: Textur verlustfrei optimieren',
                description: 'Packt verwendete UV-Pixel neu, verwendet identische Pixelmuster gemeinsam und übernimmt Box UV automatisch in per-face UV.',
                icon: 'auto_awesome',
                condition: () => !!Project && Texture.all && Texture.all.length > 0,
                click: optimizeSelectedTexture
            }));

            addAction(new Action('sms_create_detailed_blade', {
                name: 'SMS: Detaillierte Klinge erzeugen',
                description: 'Erzeugt aus einer geraden, symmetrischen Auswahl flacher Cubes beidseitige, zunehmend verjüngte Tiefen-Layer. Enddicke, Klingenschärfe und Layerzahl sind einstellbar.',
                icon: 'content_cut',
                condition: () => !!Project && Cube.selected && Cube.selected.length >= 2,
                click: openDetailedBladeDialog
            }));

            addAction(new Action('sms_restore_selection', {
                name: 'SMS: Vorherige Auswahl wiederherstellen',
                description: 'Stellt die komplette vorherige Mehrfachauswahl wieder her.',
                icon: 'history',
                click: restorePreviousSelection
            }));

            const stickyToggle = new Toggle('sms_sticky_selection', {
                name: 'SMS: Auswahl gegen Leerklick sperren',
                description: 'Verhindert, dass ein Klick in den leeren 3D-Raum die komplette Auswahl aufhebt. Andere Cubes können weiterhin bewusst ausgewählt werden.',
                icon: 'push_pin',
                value: false,
                onChange(value) {
                    state.stickySelection = !!value;
                    if (value) {
                        const now = currentSelectionUUIDs();
                        if (now.length) {
                            state.currentSelection = now.slice();
                            state.stickySelectionSnapshot = now.slice();
                        }
                        quick('SMS-Auswahlsperre AN · Leerklicks heben die Auswahl nicht mehr auf');
                    } else {
                        state.stickySelectionSnapshot = [];
                        quick('SMS-Auswahlsperre AUS');
                    }
                }
            });
            addAction(stickyToggle);

            addAction(new Action('sms_clear_selection', {
                name: 'SMS: Auswahl bewusst aufheben',
                description: 'Hebt die Auswahl auch bei eingeschalteter SMS-Auswahlsperre vollständig auf.',
                icon: 'deselect',
                click: explicitClearSelection
            }));

            addListener('update_selection', onSelectionUpdate);
            addListener('canvas_click', onCanvasClickTrackBuiltInVertexSnap);
            addListener('init_edit', onInitEditSmartMirror);
            addListener('finish_edit', onFinishEditSmartMirror);
            addListener('add_cube', onAddCubeSmartMirror);
            addListener('undo', onUndoRedoSmartMirror);
            addListener('redo', onUndoRedoSmartMirror);
            addListener('load_undo_save', onUndoRedoSmartMirror);
            addListener('select_project', () => {
                closeDuplicateReview(true);
                resetAdvancedVertexOperation(false);
                resetNativeVertexSnapWorkflow(false);
                state.pendingVertexSnapAuthority = null;
                state.mirrorAuthority.clear();
                state.currentSelection = currentSelectionUUIDs();
                state.previousSelection = [];
                state.stickySelectionSnapshot = state.stickySelection ? state.currentSelection.slice() : [];
                if (state.smartMirrorEnabled) disableNativeMirrorForProject();
                rebuildMirrorPairs();
            });

            state.currentSelection = currentSelectionUUIDs();
            state.mirrorPlane = 8;
            rebuildMirrorPairs();
            quick('Smart Modeling Suite geladen');
        },

        onunload() {
            state.smartMirrorEnabled = false;
            restoreNativeMirrorStates();
            if (state.syncTimer !== null) {
                clearTimeout(state.syncTimer);
                state.syncTimer = null;
            }
            state.syncScheduled = false;
            state.forcedMirrorUUIDs.clear();
            closeDuplicateReview(true);
            removeAllListeners();
            for (const action of actions) {
                try {
                    if (Toolbars && Toolbars.tools) Toolbars.tools.remove(action);
                } catch (_) {}
                try { action.delete(); } catch (_) {}
            }
            actions = [];
            try {
                if (state.cssHandle && typeof state.cssHandle.delete === 'function') state.cssHandle.delete();
            } catch (_) {}
            state.cssHandle = null;
            state.mirrorPairs.clear();
            state.mirrorSingles.clear();
            state.mirrorAuthority.clear();
            state.pendingVertexSnapAuthority = null;
            resetAdvancedVertexOperation(false);
            resetNativeVertexSnapWorkflow(false);
            state.cubeSnapshots.clear();
            log('Unloaded');
        }
    });
})();
