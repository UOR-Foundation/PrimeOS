/**
 * PrimeOS JavaScript Library - Framework
 * Base 1 Observation Model
 */

// Import core
const Prime = require("../../core.js");
const MathUtils = require("../math");

/**
 * Observation Model - Handles data retrieval and monitoring
 */
const ObservationModel = {
  /**
   * Create an observation model
   * @param {Object} config - Configuration object
   * @returns {Object} Observation model
   */
  create: function (config = {}) {
    return {
      type: "observation",
      sources: config.sources || [],
      filters: config.filters || [],
      name: config.name || "ObservationModel",

      /**
       * Resolve a reference to an object
       * @param {Object|string} reference - Reference to resolve
       * @returns {*} Resolved object
       */
      resolve: function (reference) {
        // Handle UOR references
        if (Prime.UOR && Prime.UOR.isReference(reference)) {
          // This is a placeholder - in a real implementation, we would
          // have a way to map references to concrete objects
          return null;
        }

        // Handle string identifiers
        if (typeof reference === "string") {
          // Look for a source with this identifier
          const source = this.sources.find((s) => s.id === reference);

          if (source) {
            return source.data;
          }
        }

        return null;
      },

      /**
       * Fetch data matching a query
       * @param {Object} query - Query to execute
       * @param {Object} [options] - Fetch options
       * @param {number} [options.limit] - Maximum number of results to return
       * @param {number} [options.offset] - Number of results to skip
       * @param {string} [options.sort] - Property to sort by
       * @param {boolean} [options.descending] - Whether to sort in descending order
       * @returns {Object} Fetch results with data and metadata
       */
      fetch: function (query, options = {}) {
        // Validate inputs
        if (!query) {
          return {
            data: [],
            meta: {
              total: 0,
              sources: 0,
              filtered: 0,
              limit: options.limit || null,
              offset: options.offset || 0,
              truncated: false,
            },
          };
        }

        // Track metadata for the query
        const meta = {
          sources: 0,
          sourceCounts: {},
          total: 0,
          filtered: 0,
          truncated: false,
          executionTime: Date.now(),
          sortingError: null,
          filterErrors: [],
        };

        // Create a type-safe query function
        const createQueryMatcher = (query) => {
          // If query is already a function, return it
          if (typeof query === "function") {
            return query;
          }

          // Create a matcher function for object queries
          return (item) => {
            if (!item || typeof item !== "object") {
              return false;
            }

            // Match all properties in query
            for (const key in query) {
              // Skip undefined query values
              if (query[key] === undefined) {
                continue;
              }

              // Handle null specially
              if (query[key] === null) {
                if (item[key] !== null) {
                  return false;
                }
                continue;
              }

              // Handle regular expressions
              if (query[key] instanceof RegExp) {
                if (
                  typeof item[key] !== "string" ||
                  !query[key].test(item[key])
                ) {
                  return false;
                }
                continue;
              }

              // Handle nested objects recursively
              if (
                typeof query[key] === "object" &&
                query[key] !== null &&
                typeof item[key] === "object" &&
                item[key] !== null
              ) {
                const nestedMatcher = createQueryMatcher(query[key]);
                if (!nestedMatcher(item[key])) {
                  return false;
                }
                continue;
              }

              // Regular value comparison with type coercion protection
              if (item[key] !== query[key]) {
                return false;
              }
            }

            return true;
          };
        };

        // Create the query matcher function
        const matcher = createQueryMatcher(query);

        // Gather candidates from all sources
        let candidates = [];

        try {
          // Process each data source
          for (const source of this.sources) {
            meta.sources++;
            meta.sourceCounts[source.id] = 0;

            try {
              // Use native query if available
              if (typeof source.query === "function") {
                const sourceResults = source.query(query);

                if (Array.isArray(sourceResults)) {
                  const resultCount = sourceResults.length;
                  meta.sourceCounts[source.id] = resultCount;
                  meta.total += resultCount;
                  candidates = candidates.concat(
                    sourceResults.map((item) => ({
                      item,
                      source: source.id,
                    })),
                  );
                }
              }
              // Otherwise, filter the source data if it's an array
              else if (Array.isArray(source.data)) {
                // Apply filtering with index-based optimization for large arrays
                const sourceData = source.data;
                const sourceLength = sourceData.length;

                // For large arrays, use chunked processing to avoid blocking
                const CHUNK_SIZE = 1000;
                const filtered = [];

                for (let i = 0; i < sourceLength; i += CHUNK_SIZE) {
                  const chunk = sourceData.slice(i, i + CHUNK_SIZE);
                  const matchingItems = chunk.filter(matcher);
                  filtered.push(...matchingItems);

                  // Early exit for queries with a limit to optimize performance
                  if (
                    options.limit &&
                    candidates.length + filtered.length >= options.limit
                  ) {
                    meta.truncated = true;
                    break;
                  }
                }

                const resultCount = filtered.length;
                meta.sourceCounts[source.id] = resultCount;
                meta.total += sourceLength;
                meta.filtered += resultCount;

                candidates = candidates.concat(
                  filtered.map((item) => ({
                    item,
                    source: source.id,
                  })),
                );
              }
            } catch (error) {
              // Log error but continue with other sources for robustness
              Prime.Logger.error(`Error querying source ${source.id}:`, error);

              // Add error to metadata
              meta.errors = meta.errors || {};
              meta.errors[source.id] = error.message;
            }
          }
        } catch (error) {
          Prime.Logger.error("Unexpected error in fetch:", error);
          throw new Prime.InvalidOperationError("Error fetching data", {
            context: { error: error.message },
          });
        }

        // Apply sorting if specified - with numerical stability improvements
        if (options.sort) {
          const sortKey = options.sort;
          const sortMultiplier = options.descending ? -1 : 1;

          try {
            // Stable sort implementation
            const stableSort = (arr, compareFn) => {
              return arr
                .map((item, index) => ({ item, index }))
                .sort((a, b) => {
                  const result = compareFn(a.item, b.item);
                  // If results are equal, maintain original order
                  return result !== 0 ? result : a.index - b.index;
                })
                .map(({ item }) => item);
            };

            // Sort with improved numerical stability
            candidates = stableSort(candidates, (a, b) => {
              const valueA = a.item[sortKey];
              const valueB = b.item[sortKey];

              // Handle undefined or null values - place at the end
              if (valueA === undefined || valueA === null) {
                return options.descending ? -1 : 1;
              }
              if (valueB === undefined || valueB === null) {
                return options.descending ? 1 : -1;
              }

              // Handle NaN values similarly to null/undefined
              if (typeof valueA === "number" && isNaN(valueA)) {
                return options.descending ? -1 : 1;
              }
              if (typeof valueB === "number" && isNaN(valueB)) {
                return options.descending ? 1 : -1;
              }

              // Type-specific stable comparisons
              if (typeof valueA === "string" && typeof valueB === "string") {
                return sortMultiplier * valueA.localeCompare(valueB);
              } else if (
                typeof valueA === "number" &&
                typeof valueB === "number"
              ) {
                // Handle special cases in floating point comparisons
                if (
                  Math.abs(valueA - valueB) <
                  MathUtils.CONSTANTS.EPSILON_GENERAL
                ) {
                  return 0; // Consider nearly equal values as equal
                }
                return sortMultiplier * (valueA - valueB);
              } else if (valueA instanceof Date && valueB instanceof Date) {
                return sortMultiplier * (valueA.getTime() - valueB.getTime());
              } else if (
                typeof valueA === "boolean" &&
                typeof valueB === "boolean"
              ) {
                return (
                  sortMultiplier * (valueA === valueB ? 0 : valueA ? 1 : -1)
                );
              } else {
                // Convert to string for default comparison
                return (
                  sortMultiplier * String(valueA).localeCompare(String(valueB))
                );
              }
            });
          } catch (error) {
            Prime.Logger.warn(
              `Sorting error: ${error.message}. Results will be returned unsorted.`,
            );
            meta.sortingError = error.message;
          }
        }

        // Apply filters in sequence
        let results = candidates.map((c) => c.item);

        for (const filter of this.filters) {
          try {
            if (typeof filter === "function") {
              results = filter(results, query);
            } else if (filter && typeof filter.apply === "function") {
              results = filter.apply(results, query);
            }

            if (!Array.isArray(results)) {
              Prime.Logger.error(
                `Filter returned non-array result: ${typeof results}`,
              );
              results = [];
              break;
            }
          } catch (error) {
            Prime.Logger.error(`Error applying filter:`, error);
            meta.filterErrors.push(error.message);
          }
        }

        // Calculate total result count before pagination
        const totalResults = results.length;

        // Apply pagination with bounds checking
        if (options.offset || options.limit) {
          const offset = Math.max(0, options.offset || 0);

          // Ensure offset is valid
          if (offset < results.length) {
            results = results.slice(
              offset,
              options.limit ? offset + options.limit : undefined,
            );
          } else {
            results = [];
          }

          // Update truncation status
          meta.truncated =
            meta.truncated ||
            totalResults > offset + (options.limit || totalResults);
        }

        // Complete the metadata
        meta.returnedCount = results.length;
        meta.executionTime = Date.now() - meta.executionTime;

        // For backwards compatibility with tests
        if (options.backwardsCompatible !== false) {
          return results;
        } else {
          return {
            data: results,
            meta: {
              ...meta,
              limit: options.limit || null,
              offset: options.offset || 0,
            },
          };
        }
      },

      /**
       * Observe a data source
       * @param {string} sourceId - Source identifier
       * @param {Object} options - Observation options
       * @returns {Object} Subscription object
       */
      observe: function (sourceId, options = {}) {
        const source = this.sources.find((s) => s.id === sourceId);

        if (!source) {
          throw new Prime.InvalidOperationError(
            `Source ${sourceId} not found`,
            {
              context: { availableSources: this.sources.map((s) => s.id) },
            },
          );
        }

        if (typeof source.subscribe !== "function") {
          throw new Prime.InvalidOperationError(
            `Source ${sourceId} does not support subscription`,
          );
        }

        return source.subscribe(options);
      },

      /**
       * Add a data source
       * @param {Object} source - Data source to add
       * @returns {Object} Updated observation model
       */
      addSource: function (source) {
        if (!source.id) {
          throw new Prime.ValidationError("Source must have an id property");
        }

        this.sources.push(source);
        return this;
      },

      /**
       * Add a filter
       * @param {Function|Object} filter - Filter to add
       * @returns {Object} Updated observation model
       */
      addFilter: function (filter) {
        this.filters.push(filter);
        return this;
      },

      /**
       * Connect to Base 0 components
       * @param {Object} base0 - Base 0 components
       * @returns {Object} Connected observation model
       */
      connectToBase0: function (base0) {
        this._base0 = base0;
        return this;
      },
    };
  },
};

module.exports = ObservationModel;
