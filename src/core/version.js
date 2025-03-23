/**
 * PrimeOS JavaScript Library - Version Management
 * Semantic versioning and comparison utilities
 * Version 1.0.0
 */

// Import Prime object from prime.js
const Prime = require('./prime.js');

(function (Prime) {
  // Version management utilities
  const VersionUtils = {
    /**
     * Parses a semantic version string into its components
     * @param {string} version - Version string to parse (e.g., "1.2.3-alpha.1+build.456")
     * @returns {Object|null} Parsed version object or null if invalid
     */
    parseVersion: (version) => {
      if (typeof version !== 'string') return null;

      // Regular expression for SemVer 2.0.0 (major.minor.patch-prerelease+build)
      const semverRegex =
        /^(0|[1-9]\d*)\.?(0|[1-9]\d*)\.?(0|[1-9]\d*)?(?:-((?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*)(?:\.(?:0|[1-9]\d*|\d*[a-zA-Z-][0-9a-zA-Z-]*))*))?(?:\+([0-9a-zA-Z-]+(?:\.[0-9a-zA-Z-]+)*))?$/;

      const match = version.trim().match(semverRegex);
      if (!match) return null;

      const [, majorStr, minorStr, patchStr, prereleaseStr, buildStr] = match;

      // Convert version parts to numbers, handling undefined
      const major = parseInt(majorStr, 10);
      const minor = minorStr !== undefined ? parseInt(minorStr, 10) : 0;
      const patch = patchStr !== undefined ? parseInt(patchStr, 10) : 0;

      // Parse prerelease identifiers
      const prerelease = prereleaseStr ? prereleaseStr.split('.') : [];

      // Parse build metadata
      const build = buildStr ? buildStr.split('.') : [];

      return {
        major,
        minor,
        patch,
        prerelease,
        build,
        original: version,
      };
    },

    /**
     * Compares two version strings according to semantic versioning rules
     * @param {string} v1 - First version string
     * @param {string} v2 - Second version string
     * @returns {number} -1 if v1 < v2, 0 if v1 = v2, 1 if v1 > v2, or null if invalid
     */
    compareVersions: (v1, v2) => {
      const parsedV1 = VersionUtils.parseVersion(v1);
      const parsedV2 = VersionUtils.parseVersion(v2);

      // Check if both versions are valid
      if (!parsedV1 || !parsedV2) {
        return null;
      }

      // Compare major.minor.patch
      if (parsedV1.major !== parsedV2.major) {
        return parsedV1.major > parsedV2.major ? 1 : -1;
      }
      if (parsedV1.minor !== parsedV2.minor) {
        return parsedV1.minor > parsedV2.minor ? 1 : -1;
      }
      if (parsedV1.patch !== parsedV2.patch) {
        return parsedV1.patch > parsedV2.patch ? 1 : -1;
      }

      // If we get here, the main version components are equal
      // A version with a prerelease component is always lower than a version without
      if (parsedV1.prerelease.length === 0 && parsedV2.prerelease.length > 0) {
        return 1;
      }
      if (parsedV1.prerelease.length > 0 && parsedV2.prerelease.length === 0) {
        return -1;
      }
      if (
        parsedV1.prerelease.length === 0 &&
        parsedV2.prerelease.length === 0
      ) {
        return 0;
      }

      // Both have prerelease components, compare them
      const minLength = Math.min(
        parsedV1.prerelease.length,
        parsedV2.prerelease.length,
      );
      for (let i = 0; i < minLength; i++) {
        const a = parsedV1.prerelease[i];
        const b = parsedV2.prerelease[i];

        // If both are numeric, compare as numbers
        const aNum = parseInt(a, 10);
        const bNum = parseInt(b, 10);
        if (!isNaN(aNum) && !isNaN(bNum)) {
          if (aNum !== bNum) {
            return aNum > bNum ? 1 : -1;
          }
        } else {
          // If one is numeric and the other is not, numeric always has lower precedence
          if (!isNaN(aNum) && isNaN(bNum)) return -1;
          if (isNaN(aNum) && !isNaN(bNum)) return 1;

          // Both are strings, compare lexicographically
          if (a !== b) {
            return a > b ? 1 : -1;
          }
        }
      }

      // If one prerelease array is longer than the other, the longer one has higher precedence
      if (parsedV1.prerelease.length !== parsedV2.prerelease.length) {
        return parsedV1.prerelease.length > parsedV2.prerelease.length ? 1 : -1;
      }

      // The versions are equal
      return 0;
    },

    /**
     * Checks if a version is compatible with a version range
     * @param {string} version - Version to check
     * @param {string} range - Version range (e.g., ">=1.2.0 <2.0.0")
     * @returns {boolean} True if compatible, false otherwise
     */
    isCompatible: (version, range) => {
      // Convert simple ranges to canonical form
      if (/^\d+\.\d+\.\d+$/.test(range)) {
        range = `=${range}`;
      }

      // Parse version
      const parsedVersion = VersionUtils.parseVersion(version);
      if (!parsedVersion) return false;

      // Split range into individual comparators
      const comparators = range
        .split(/\s+/)
        .filter((comp) => comp.trim().length > 0);

      // Check all comparators
      return comparators.every((comparator) => {
        // Extract operator and version
        const match = comparator.match(/^([<>=~^]*)(.+)$/);
        if (!match) return false;

        const [, operator, compareVersion] = match;
        const parsedCompareVersion = VersionUtils.parseVersion(compareVersion);
        if (!parsedCompareVersion) return false;

        const result = VersionUtils.compareVersions(
          version,
          parsedCompareVersion.original,
        );

        switch (operator) {
          case '=':
          case '':
            return result === 0;
          case '>':
            return result === 1;
          case '>=':
            return result === 1 || result === 0;
          case '<':
            return result === -1;
          case '<=':
            return result === -1 || result === 0;
          case '~':
            return (
              parsedVersion.major === parsedCompareVersion.major &&
              parsedVersion.minor === parsedCompareVersion.minor &&
              parsedVersion.patch >= parsedCompareVersion.patch
            );
          case '^':
            return (
              parsedVersion.major === parsedCompareVersion.major &&
              (parsedVersion.minor > parsedCompareVersion.minor ||
                (parsedVersion.minor === parsedCompareVersion.minor &&
                  parsedVersion.patch >= parsedCompareVersion.patch))
            );
          default:
            return false;
        }
      });
    },
  };

  // Add version validation functions to Prime
  
  /**
   * Validates if a version string is compatible with the current version
   * @param {string} version - Version string to validate
   * @returns {boolean} True if version is valid and compatible
   */
  Prime.validateVersion = function(version) {
    try {
      const parsed = VersionUtils.parseVersion(version);
      if (!parsed) return false;
      
      // Extract current version
      const current = VersionUtils.parseVersion(Prime.VERSION || '1.0.0');
      if (!current) return false;
      
      // Higher major version should be invalid
      if (parsed.major > current.major) return false;
      
      // All other versions are considered valid
      return true;
    } catch (e) {
      return false;
    }
  };
  
  /**
   * Validates a version with partial matching (e.g., just major.minor)
   * @param {string} version - Partial version string
   * @returns {boolean} True if version is compatible
   */
  Prime.validateVersionPartial = function(version) {
    try {
      // Handle invalid version strings
      if (typeof version !== 'string') return false;
      
      // Add .0 for partial versions
      const fullVersion = version.split('.').length < 3 
        ? `${version}${'0'.repeat(3 - version.split('.').length)}` 
        : version;
      
      return Prime.validateVersion(fullVersion);
    } catch (e) {
      return false;
    }
  };
  
  /**
   * Checks compatibility with minimum version and feature requirements
   * @param {Object} requirements - Compatibility requirements
   * @param {string} requirements.minVersion - Minimum required version
   * @param {string[]} [requirements.features] - Required features
   * @returns {boolean} True if compatible with requirements
   */
  Prime.isCompatible = function(requirements) {
    try {
      // Validate input - handle null more safely
      if (!requirements) {
        return false;
      }
      
      // Handle core.js isCompatible implementation
      if (typeof requirements === 'object') {
        const features = requirements.features || [];
        const minVersion = requirements.minVersion || '0.0.0';
        
        // Check version
        if (!Prime.validateVersion(minVersion)) {
          return false;
        }
        
        // Check features
        if (Array.isArray(features) && features.length > 0) {
          // Use feature map from parent object
          for (const feature of features) {
            if (!Prime.features[feature]) {
              return false;
            }
          }
        }
        
        return true;
      }
      
      return false;
    } catch (e) {
      return false;
    }
  };
  
  // Initialize features object
  Prime.features = {
    core: true,
    utils: true,
    events: true,
    logging: true,
    versionManagement: true
  };
  
  // Expose version utilities directly on Prime
  Prime.compareVersions = VersionUtils.compareVersions;
  Prime.parseVersion = function(version) {
    const parsed = VersionUtils.parseVersion(version);
    if (!parsed) {
      throw new Prime.ValidationError('Invalid version format');
    }
    return {
      major: parsed.major,
      minor: parsed.minor,
      patch: parsed.patch
    };
  };
  
  // Add version utilities to Prime.Utils
  Prime.Utils.VersionUtils = VersionUtils;
})(Prime);

// CommonJS export
if (typeof module !== 'undefined' && module.exports) {
  module.exports = Prime;
}
