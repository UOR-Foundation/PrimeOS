/**
 * PrimeOS JavaScript Library - Framework
 * Base 1: Resource
 * Concrete implementations of Base 0 models
 */

// Import core
const Prime = require("../../core/prime.js");
const MathUtils = require("../math");

// Import runtime and observation models
const RuntimeModel = require("./runtime");
const ObservationModel = require("./observation");
const InteractionModel = require("./interaction");
const RepresentationModel = require("./representation");

/**
 * Base 1: Resource
 * Concrete implementations of Base 0 models
 */
const Base1 = {
  /**
   * Create a runtime model
   * @param {Object} config - Configuration object
   * @returns {Object} Runtime model
   */
  createRuntimeModel: function (config = {}) {
    return RuntimeModel.create(config);
  },

  /**
   * Create an observation model
   * @param {Object} config - Configuration object
   * @returns {Object} Observation model
   */
  createObservationModel: function (config = {}) {
    return ObservationModel.create(config);
  },

  /**
   * Create an interaction model
   * @param {Object} config - Configuration object
   * @returns {Object} Interaction model
   */
  createInteractionModel: function (config = {}) {
    return InteractionModel.create(config);
  },

  /**
   * Create a representation model
   * @param {Object} config - Configuration object
   * @returns {Object} Representation model
   */
  createRepresentationModel: function (config = {}) {
    return RepresentationModel.create(config);
  },

  /**
   * Connect to Base 0
   * @param {Object} base0Components - Base 0 components
   * @returns {Object} Connected Base 1 resources
   */
  connectToBase0: function (base0Components) {
    return {
      runtime: this.createRuntimeModel({}).connectToBase0(base0Components),
      observation: this.createObservationModel({}).connectToBase0(
        base0Components,
      ),
      interaction: this.createInteractionModel({}).connectToBase0(
        base0Components,
      ),
      representation: this.createRepresentationModel({}).connectToBase0(
        base0Components,
      ),
    };
  },
};

module.exports = Base1;
