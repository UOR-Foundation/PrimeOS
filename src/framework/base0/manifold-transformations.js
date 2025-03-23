/**
 * PrimeOS JavaScript Library - Framework
 * Base 0: Manifold Transformations
 * Operations that transform manifolds
 */

// Import core
const Prime = require('../../core.js');
const MathUtils = require('../math');
const { Manifold } = require('./manifold.js');

/**
 * ManifoldTransformations - Transformations for manifolds
 */
const ManifoldTransformations = {
  /**
   * Align a manifold with another target manifold
   * @param {Manifold} source - Source manifold to align
   * @param {Manifold} target - Target manifold to align with
   * @param {Object} options - Alignment options
   * @returns {Manifold} Aligned manifold
   */
  alignWith: function (source, target, options = {}) {
    if (!(source instanceof Manifold) || !(target instanceof Manifold)) {
      throw new Prime.ValidationError('Source and target must be manifolds');
    }

    const strategy = options.strategy || 'projection';

    // Different alignment strategies
    if (strategy === 'projection') {
      // Simple projection alignment
      const commonSpaces = source
        .getSpaces()
        .filter((space) => target.getSpaces().includes(space));

      if (commonSpaces.length === 0) {
        throw new Prime.InvalidOperationError(
          'Manifolds must share at least one space for projection alignment',
        );
      }

      const space = commonSpaces[0];

      // Project source to the common space
      const aligned = source.project(space, (manifold) => {
        // Create a new variant that aligns with target's structure
        const sourceVariant = source.getVariant();
        const targetVariant = target.getVariant();

        // Initialize with source's variant
        const alignedVariant = { ...sourceVariant };

        // Adapt keys from the target when present in both
        for (const key in targetVariant) {
          if (sourceVariant.hasOwnProperty(key)) {
            const sourceVal = sourceVariant[key];
            const targetVal = targetVariant[key];

            // For numeric values, maintain the source's scale but align to target's structure
            if (
              typeof sourceVal === 'number' &&
              typeof targetVal === 'number'
            ) {
              if (targetVal !== 0) {
                // Scale source value to target's magnitude while preserving direction
                const scaleFactor = Math.abs(sourceVal) / Math.abs(targetVal);
                alignedVariant[key] = targetVal * scaleFactor;
              }
            } else if (Array.isArray(sourceVal) && Array.isArray(targetVal)) {
              // For arrays, align dimensions when possible
              if (sourceVal.length === targetVal.length) {
                // Align vectors using mathematical alignment
                const dotProduct = MathUtils.vector.cosineSimilarity(
                  sourceVal,
                  targetVal,
                );
                if (Math.abs(dotProduct.similarity) > 0.1) {
                  // Use the target's direction with source's magnitude
                  const sourceNorm = MathUtils.vector.norm(sourceVal);
                  const targetNormalized =
                    MathUtils.vector.normalizeSimple(targetVal);
                  alignedVariant[key] = targetNormalized.map(
                    (v) => v * sourceNorm,
                  );
                }
              }
            }
          }
        }

        return {
          invariant: source.getInvariant(),
          variant: alignedVariant,
          meta: {
            ...source.getMeta(),
            alignedTo: target.getId(),
            alignmentStrategy: 'projection',
          },
        };
      });

      // Establish relation to the target
      aligned.relateTo(target, 'aligned_to');

      return aligned;
    } else if (strategy === 'transformation') {
      // Transformation-based alignment
      // Compute a transformation that maps source to target
      const sourceVariant = source.getVariant();
      const targetVariant = target.getVariant();

      // Create a new manifold with transformed properties
      const meta = {
        ...source.getMeta(),
        id: `aligned_${source.getId()}_to_${target.getId()}`,
        alignedTo: target.getId(),
        alignmentStrategy: strategy,
      };

      // Keep the original invariant properties
      const invariant = source.getInvariant();

      // Create transformed variant properties
      const variant = { ...sourceVariant };

      // Determine transformation parameters
      const sourceNumeric = Object.entries(sourceVariant)
        .filter(([_, val]) => typeof val === 'number')
        .map(([key, val]) => ({ key, val }));

      const targetNumeric = Object.entries(targetVariant)
        .filter(([_, val]) => typeof val === 'number')
        .map(([key, val]) => ({ key, val }));

      // Calculate simple transformation parameters
      if (sourceNumeric.length > 0 && targetNumeric.length > 0) {
        // Compute average scale difference
        let scaleSum = 0;
        let scaleCount = 0;

        for (const { key: sourceKey, val: sourceVal } of sourceNumeric) {
          for (const { key: targetKey, val: targetVal } of targetNumeric) {
            if (sourceKey === targetKey && sourceVal !== 0 && targetVal !== 0) {
              scaleSum += Math.abs(targetVal / sourceVal);
              scaleCount++;
            }
          }
        }

        // Apply transformation if we have valid scale information
        if (scaleCount > 0) {
          const averageScale = scaleSum / scaleCount;

          // Apply scaling to all numeric properties
          for (const key in variant) {
            if (typeof variant[key] === 'number') {
              variant[key] *= averageScale;
            } else if (
              Array.isArray(variant[key]) &&
              variant[key].every((v) => typeof v === 'number')
            ) {
              variant[key] = variant[key].map((v) => v * averageScale);
            }
          }
        }
      }

      // Create the aligned manifold
      const aligned = new Manifold({
        meta,
        invariant,
        variant,
        depth: source.depth,
        spaces: source.getSpaces(),
      });

      // Establish relation to the target
      aligned.relateTo(target, 'aligned_to');

      return aligned;
    }

    throw new Prime.InvalidOperationError(
      `Alignment strategy ${strategy} not supported in this context`,
    );
  },

  /**
   * Scale a manifold by a factor
   * @param {Manifold} manifold - Manifold to scale
   * @param {number} factor - Scale factor to apply
   * @param {Object} options - Scaling options
   * @returns {Manifold} Scaled manifold
   */
  scale: function (manifold, factor, options = {}) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError('First argument must be a manifold');
    }

    if (typeof factor !== 'number' || !isFinite(factor)) {
      throw new Prime.ValidationError('Factor must be a finite number');
    }

    // Properties to include in scaling
    const includeProps = options.properties || null;
    const excludeProps = options.exclude || [];

    // Create a new manifold with scaled properties
    const meta = {
      ...manifold.getMeta(),
      id: `scaled_${manifold.getId()}_by_${factor}`,
      scaledFrom: manifold.getId(),
      scaleFactor: factor,
    };

    // Keep the original invariant properties
    const invariant = manifold.getInvariant();

    // Create scaled variant properties
    const originalVariant = manifold.getVariant();
    const variant = { ...originalVariant };

    // Scale numeric and array properties
    for (const key in variant) {
      // Skip excluded properties
      if (excludeProps.includes(key)) {
        continue;
      }

      // Only include specific properties if provided
      if (includeProps !== null && !includeProps.includes(key)) {
        continue;
      }

      const value = variant[key];

      if (typeof value === 'number') {
        variant[key] = value * factor;
      } else if (
        Array.isArray(value) &&
        value.every((v) => typeof v === 'number')
      ) {
        variant[key] = value.map((v) => v * factor);
      }
    }

    // Create the scaled manifold
    const scaled = new Manifold({
      meta,
      invariant,
      variant,
      depth: manifold.getDepth(),
      spaces: manifold.getSpaces(),
    });

    // Establish relation to the original
    scaled.relateTo(manifold, 'scaled_from', { factor });

    return scaled;
  },

  /**
   * Rotate a manifold's vector properties
   * @param {Manifold} manifold - Manifold to rotate
   * @param {Object} options - Rotation options
   * @returns {Manifold} Rotated manifold
   */
  rotate: function (manifold, options = {}) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError('First argument must be a manifold');
    }

    // Get the vector properties to rotate
    const properties = options.properties || [];
    const angles = options.angles || [];

    if (properties.length === 0) {
      throw new Prime.ValidationError('No properties specified for rotation');
    }

    if (angles.length === 0) {
      throw new Prime.ValidationError('No rotation angles specified');
    }

    // Create a new manifold with rotated properties
    const meta = {
      ...manifold.getMeta(),
      id: `rotated_${manifold.getId()}`,
      rotatedFrom: manifold.getId(),
      rotationAngles: angles,
    };

    // Keep the original invariant properties
    const invariant = manifold.getInvariant();

    // Create rotated variant properties
    const originalVariant = manifold.getVariant();
    const variant = { ...originalVariant };

    // Rotate vector properties
    for (const prop of properties) {
      const value = variant[prop];

      if (Array.isArray(value) && value.every((v) => typeof v === 'number')) {
        // Only handle 2D and 3D rotation for simplicity
        if (value.length === 2) {
          // 2D rotation
          const angle = angles[0] || 0;
          const cos = Math.cos(angle);
          const sin = Math.sin(angle);

          variant[prop] = [
            value[0] * cos - value[1] * sin,
            value[0] * sin + value[1] * cos,
          ];
        } else if (value.length === 3) {
          // 3D rotation (simplified - using Euler angles)
          const angleX = angles[0] || 0;
          const angleY = angles[1] || 0;
          const angleZ = angles[2] || 0;

          // Create rotation matrices
          const rotX = [
            [1, 0, 0],
            [0, Math.cos(angleX), -Math.sin(angleX)],
            [0, Math.sin(angleX), Math.cos(angleX)],
          ];

          const rotY = [
            [Math.cos(angleY), 0, Math.sin(angleY)],
            [0, 1, 0],
            [-Math.sin(angleY), 0, Math.cos(angleY)],
          ];

          const rotZ = [
            [Math.cos(angleZ), -Math.sin(angleZ), 0],
            [Math.sin(angleZ), Math.cos(angleZ), 0],
            [0, 0, 1],
          ];

          // Apply rotation matrices (Z * Y * X * vector)
          const result = [0, 0, 0];

          // Apply X rotation
          const temp = [0, 0, 0];
          for (let i = 0; i < 3; i++) {
            for (let j = 0; j < 3; j++) {
              temp[i] += rotX[i][j] * value[j];
            }
          }

          // Apply Y rotation
          const temp2 = [0, 0, 0];
          for (let i = 0; i < 3; i++) {
            for (let j = 0; j < 3; j++) {
              temp2[i] += rotY[i][j] * temp[j];
            }
          }

          // Apply Z rotation
          for (let i = 0; i < 3; i++) {
            for (let j = 0; j < 3; j++) {
              result[i] += rotZ[i][j] * temp2[j];
            }
          }

          variant[prop] = result;
        }
      }
    }

    // Create the rotated manifold
    const rotated = new Manifold({
      meta,
      invariant,
      variant,
      depth: manifold.getDepth(),
      spaces: manifold.getSpaces(),
    });

    // Establish relation to the original
    rotated.relateTo(manifold, 'rotated_from', { angles });

    return rotated;
  },

  /**
   * Mirror a manifold across an axis/plane
   * @param {Manifold} manifold - Manifold to mirror
   * @param {Object} options - Mirroring options
   * @returns {Manifold} Mirrored manifold
   */
  mirror: function (manifold, options = {}) {
    if (!(manifold instanceof Manifold)) {
      throw new Prime.ValidationError('First argument must be a manifold');
    }

    // Get the vector properties to mirror
    const properties = options.properties || [];
    const axis = options.axis || 0; // Axis to mirror across (index)

    if (properties.length === 0) {
      throw new Prime.ValidationError('No properties specified for mirroring');
    }

    // Create a new manifold with mirrored properties
    const meta = {
      ...manifold.getMeta(),
      id: `mirrored_${manifold.getId()}`,
      mirroredFrom: manifold.getId(),
      mirrorAxis: axis,
    };

    // Keep the original invariant properties
    const invariant = manifold.getInvariant();

    // Create mirrored variant properties
    const originalVariant = manifold.getVariant();
    const variant = { ...originalVariant };

    // Mirror vector properties
    for (const prop of properties) {
      const value = variant[prop];

      if (Array.isArray(value) && value.every((v) => typeof v === 'number')) {
        // Create a copy of the array
        const mirrored = [...value];

        // Mirror across the specified axis
        if (axis < mirrored.length) {
          mirrored[axis] = -mirrored[axis];
        }

        variant[prop] = mirrored;
      }
    }

    // Create the mirrored manifold
    const mirrored = new Manifold({
      meta,
      invariant,
      variant,
      depth: manifold.getDepth(),
      spaces: manifold.getSpaces(),
    });

    // Establish relation to the original
    mirrored.relateTo(manifold, 'mirrored_from', { axis });

    return mirrored;
  },
};

module.exports = ManifoldTransformations;
