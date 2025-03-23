/**
 * Decision Making - Coherence-based action selection
 *
 * This module implements the decision making framework needed for consciousness
 * simulation, allowing systems to select actions based on coherence maximization.
 *
 * Key features:
 * - Uses coherence metrics to evaluate decision alternatives
 * - Implements multi-perspective evaluation using fiber algebra
 * - Provides certainty metrics for decisions
 * - Tracks decision history and outcomes
 */

// Try to import core if available
let Prime;
try {
  Prime = require('../core.js');
} catch (e) {
  // Handle case where core isn't available yet
  Prime = {};
}

// Import required modules
const MathUtils = require('../framework/math/index.js');

/**
 * DecisionMaking provides mechanisms for coherence-based action selection
 */
class DecisionMaking {
  /**
   * Create a new decision making system
   *
   * @param {Object} options - Configuration options
   * @param {number} options.perspectives - Number of perspectives to evaluate (default: 3)
   * @param {number} options.coherenceThreshold - Minimum coherence threshold (default: 0.7)
   * @param {number} options.indecisionThreshold - Threshold for indecision (default: 0.1)
   * @param {number} options.explorationRate - Exploration vs exploitation rate (default: 0.2)
   * @param {Object} options.valueWeights - Weights for different value dimensions (default: balanced)
   */
  constructor(options = {}) {
    this.perspectives = options.perspectives || 3;
    this.coherenceThreshold = options.coherenceThreshold || 0.7;
    this.indecisionThreshold = options.indecisionThreshold || 0.1;
    this.explorationRate = options.explorationRate || 0.2;

    // Weights for different value dimensions in decision making
    this.valueWeights = options.valueWeights || {
      coherence: 0.4, // Coherence with existing state/beliefs
      utility: 0.3, // Expected utility
      confidence: 0.2, // Confidence in prediction
      novelty: 0.1, // Novelty/exploration value
    };

    // Decision history
    this.decisionHistory = [];
    this.outcomeHistory = [];

    // Perspective models for multi-perspective evaluation
    this._perspectiveModels = [];
    this._lastPerspectiveUpdate = Date.now();

    // Active deliberation
    this._activeDeliberation = null;

    // Performance tracking
    this._stats = {
      decisionsCount: 0,
      deliberationsCount: 0,
      evaluationsCount: 0,
      totalDecisionTime: 0,
      coherentDecisions: 0,
      explorationDecisions: 0,
    };
  }

  /**
   * Initialize decision making system
   *
   * @param {Object} state - Initial consciousness state
   * @returns {boolean} Success flag
   */
  initialize(state) {
    if (!state) {
      return false;
    }

    // Create initial perspective models
    this._createPerspectiveModels(state);

    return true;
  }

  /**
   * Make a decision between alternatives
   *
   * @param {Array} alternatives - Decision alternatives
   * @param {Object} state - Current consciousness state
   * @param {Object} [context={}] - Decision context
   * @returns {Object} Decision result
   */
  decide(alternatives, state, context = {}) {
    const startTime = Date.now();
    this._stats.decisionsCount++;

    // Handle edge cases
    if (!alternatives || alternatives.length === 0) {
      return {
        selected: null,
        alternatives: [],
        certainty: 0,
        coherence: 0,
        explanation: 'No alternatives provided',
        timestamp: Date.now(),
      };
    }

    if (alternatives.length === 1) {
      return {
        selected: alternatives[0],
        alternatives: [],
        certainty: 1.0,
        coherence: 1.0,
        explanation: 'Only one alternative available',
        timestamp: Date.now(),
      };
    }

    // Update perspective models if needed
    if (this._shouldUpdatePerspectives(state)) {
      this._updatePerspectiveModels(state);
    }

    // Check if this is a fast automatic decision or requires deliberation
    const requiresDeliberation = this._requiresDeliberation(
      alternatives,
      state,
      context,
    );

    // Make decision
    let decision;

    if (requiresDeliberation) {
      decision = this._makeDeliberativeDecision(alternatives, state, context);
    } else {
      decision = this._makeFastDecision(alternatives, state, context);
    }

    // Record decision
    this._recordDecision(decision, state, context);

    // Update stats
    this._stats.totalDecisionTime += Date.now() - startTime;

    if (decision.coherence >= this.coherenceThreshold) {
      this._stats.coherentDecisions++;
    }

    if (decision.exploration) {
      this._stats.explorationDecisions++;
    }

    return decision;
  }

  /**
   * Start deliberation about a decision
   *
   * @param {Array} alternatives - Decision alternatives
   * @param {Object} state - Current consciousness state
   * @param {Object} [context={}] - Decision context
   * @returns {Object} Deliberation state
   */
  startDeliberation(alternatives, state, context = {}) {
    this._stats.deliberationsCount++;

    // Create a new deliberation
    const deliberationId = `delib_${Date.now()}_${Math.floor(Math.random() * 10000)}`;

    // Initialize evaluations for each alternative
    const evaluations = alternatives.map((alt) => ({
      alternative: alt,
      evaluations: [],
      coherenceScores: [],
      utilityScores: [],
      confidenceScores: [],
      noveltyScores: [],
      meanCoherence: 0,
      uncertainty: 1.0,
    }));

    // Create deliberation state
    const deliberation = {
      id: deliberationId,
      alternatives,
      evaluations,
      perspectives: this._perspectiveModels.map((p) => p.id),
      startTime: Date.now(),
      completionTime: null,
      completed: false,
      iterations: 0,
      maxIterations: Math.max(5, Math.min(20, alternatives.length * 2)),
      state: { ...state },
      context: { ...context },
    };

    // Store active deliberation
    this._activeDeliberation = deliberation;

    return deliberation;
  }

  /**
   * Continue deliberation with additional evaluation
   *
   * @returns {Object} Updated deliberation
   */
  continueDeliberation() {
    if (!this._activeDeliberation) {
      return null;
    }

    // Check if deliberation is already complete
    if (this._activeDeliberation.completed) {
      return this._activeDeliberation;
    }

    // Get current deliberation
    const deliberation = this._activeDeliberation;

    // Continue with another iteration
    this._deliberationIteration(deliberation);

    // Check if we should complete deliberation
    if (deliberation.iterations >= deliberation.maxIterations) {
      this._completeDeliberation(deliberation);
    }

    return deliberation;
  }

  /**
   * Complete active deliberation and make decision
   *
   * @returns {Object} Decision result
   */
  completeDeliberation() {
    if (!this._activeDeliberation) {
      return null;
    }

    // Complete the deliberation if not already completed
    if (!this._activeDeliberation.completed) {
      this._completeDeliberation(this._activeDeliberation);
    }

    // Make final decision based on deliberation
    const decision = this._decideFromDeliberation(this._activeDeliberation);

    // Record decision
    this._recordDecision(
      decision,
      this._activeDeliberation.state,
      this._activeDeliberation.context,
    );

    // Clear active deliberation
    const completedDeliberation = this._activeDeliberation;
    this._activeDeliberation = null;

    // Return decision with reference to deliberation
    return {
      ...decision,
      deliberation: completedDeliberation.id,
    };
  }

  /**
   * Perform one iteration of deliberation
   *
   * @private
   * @param {Object} deliberation - Deliberation to continue
   */
  _deliberationIteration(deliberation) {
    deliberation.iterations++;
    this._stats.evaluationsCount++;

    // Choose a perspective for this iteration
    const perspectiveIdx = Math.floor(
      Math.random() * this._perspectiveModels.length,
    );
    const perspective = this._perspectiveModels[perspectiveIdx];

    // Choose an alternative to evaluate
    // Prioritize alternatives with fewer evaluations or high uncertainty
    const alternativeIdxs = deliberation.evaluations
      .map((evalItem, idx) => ({
        idx,
        count: evalItem.evaluations.length,
        uncertainty: evalItem.uncertainty,
      }))
      .sort((a, b) => {
        // First by count, then by uncertainty
        if (a.count !== b.count) {
          return a.count - b.count;
        }
        return b.uncertainty - a.uncertainty;
      })
      .map((item) => item.idx);

    // Take the first few alternatives
    const candidateIdxs = alternativeIdxs.slice(
      0,
      Math.ceil(deliberation.alternatives.length / 2),
    );

    // Randomly choose from candidates
    const alternativeIdx =
      candidateIdxs[Math.floor(Math.random() * candidateIdxs.length)];
    const evaluationItem = deliberation.evaluations[alternativeIdx];
    const alternative = deliberation.alternatives[alternativeIdx];

    // Perform evaluation from this perspective
    const evaluation = this._evaluateFromPerspective(
      alternative,
      deliberation.state,
      deliberation.context,
      perspective,
    );

    // Store evaluation
    evaluationItem.evaluations.push({
      perspectiveId: perspective.id,
      iteration: deliberation.iterations,
      ...evaluation,
    });

    // Update scores
    evaluationItem.coherenceScores.push(evaluation.coherence);
    evaluationItem.utilityScores.push(evaluation.utility);
    evaluationItem.confidenceScores.push(evaluation.confidence);
    evaluationItem.noveltyScores.push(evaluation.novelty);

    // Update aggregated metrics
    evaluationItem.meanCoherence =
      evaluationItem.coherenceScores.reduce((sum, val) => sum + val, 0) /
      evaluationItem.coherenceScores.length;

    // Update uncertainty (standard deviation of coherence scores)
    if (evaluationItem.coherenceScores.length > 1) {
      const mean = evaluationItem.meanCoherence;
      const variance =
        evaluationItem.coherenceScores.reduce(
          (sum, val) => sum + Math.pow(val - mean, 2),
          0,
        ) / evaluationItem.coherenceScores.length;
      evaluationItem.uncertainty = Math.sqrt(variance);
    } else {
      evaluationItem.uncertainty = 0.5; // Default uncertainty with single evaluation
    }
  }

  /**
   * Complete deliberation and aggregate results
   *
   * @private
   * @param {Object} deliberation - Deliberation to complete
   */
  _completeDeliberation(deliberation) {
    // Finalize all evaluations
    for (const evaluation of deliberation.evaluations) {
      // Compute aggregated scores
      evaluation.overallScore = this._computeOverallScore(
        evaluation.coherenceScores,
        evaluation.utilityScores,
        evaluation.confidenceScores,
        evaluation.noveltyScores,
      );
    }

    // Mark as completed
    deliberation.completed = true;
    deliberation.completionTime = Date.now();
  }

  /**
   * Make decision based on completed deliberation
   *
   * @private
   * @param {Object} deliberation - Completed deliberation
   * @returns {Object} Decision result
   */
  _decideFromDeliberation(deliberation) {
    // Sort alternatives by overall score
    const sortedEvals = [...deliberation.evaluations].sort(
      (a, b) => b.overallScore - a.overallScore,
    );

    // Get top alternative
    const topEval = sortedEvals[0];
    const topAltIdx = deliberation.evaluations.indexOf(topEval);
    const topAlt = deliberation.alternatives[topAltIdx];

    // Check if exploration should override
    let selectedAlt = topAlt;
    let isExploration = false;

    // If top evaluation has low coherence and we have exploration tendency,
    // potentially choose a different alternative
    if (
      topEval.meanCoherence < this.coherenceThreshold &&
      Math.random() < this.explorationRate
    ) {
      // Get alternatives with reasonable scores
      const viableAlts = sortedEvals
        .filter((e) => e.overallScore > sortedEvals[0].overallScore * 0.7)
        .map((e) => {
          const idx = deliberation.evaluations.indexOf(e);
          return {
            alternative: deliberation.alternatives[idx],
            novelty:
              e.noveltyScores.reduce((sum, val) => sum + val, 0) /
              e.noveltyScores.length,
            idx,
          };
        })
        .sort((a, b) => b.novelty - a.novelty);

      // If we have other viable alternatives, possibly choose the most novel one
      if (viableAlts.length > 1) {
        selectedAlt = viableAlts[0].alternative;
        isExploration = true;
      }
    }

    // Calculate certainty metric
    const selectedEval = deliberation.evaluations.find(
      (e) =>
        deliberation.alternatives[deliberation.evaluations.indexOf(e)] ===
        selectedAlt,
    );

    const certainty = this._calculateCertainty(selectedEval, sortedEvals);

    // Create decision result
    return {
      selected: selectedAlt,
      alternatives: deliberation.alternatives
        .filter((alt) => alt !== selectedAlt)
        .map((alt, idx) => {
          const evalIdx = deliberation.alternatives.indexOf(alt);
          return {
            alternative: alt,
            score: deliberation.evaluations[evalIdx].overallScore,
            coherence: deliberation.evaluations[evalIdx].meanCoherence,
          };
        }),
      certainty,
      coherence: selectedEval.meanCoherence,
      explanation: this._generateExplanation(selectedEval, isExploration),
      exploration: isExploration,
      timestamp: Date.now(),
    };
  }

  /**
   * Make a fast decision without full deliberation
   *
   * @private
   * @param {Array} alternatives - Decision alternatives
   * @param {Object} state - Current consciousness state
   * @param {Object} context - Decision context
   * @returns {Object} Decision result
   */
  _makeFastDecision(alternatives, state, context) {
    // Fast decisions use only the primary perspective
    const perspective = this._perspectiveModels[0];

    // Evaluate each alternative
    const evaluations = alternatives.map((alt) =>
      this._evaluateFromPerspective(alt, state, context, perspective),
    );

    // Calculate overall scores
    const withScores = evaluations.map((evalItem, idx) => ({
      alternative: alternatives[idx],
      evaluation: evalItem,
      score: this._computeOverallScore(
        [evalItem.coherence],
        [evalItem.utility],
        [evalItem.confidence],
        [evalItem.novelty],
      ),
    }));

    // Sort by score
    withScores.sort((a, b) => b.score - a.score);

    // Get top alternative
    const topChoice = withScores[0];

    // Check if exploration should override
    let selectedChoice = topChoice;
    let isExploration = false;

    // If top evaluation has low coherence and we have exploration tendency,
    // potentially choose a different alternative
    if (
      topChoice.evaluation.coherence < this.coherenceThreshold &&
      Math.random() < this.explorationRate
    ) {
      // Get alternatives with reasonable scores
      const viableChoices = withScores
        .filter((item) => item.score > topChoice.score * 0.7)
        .sort((a, b) => b.evaluation.novelty - a.evaluation.novelty);

      // If we have other viable alternatives, possibly choose the most novel one
      if (viableChoices.length > 1) {
        selectedChoice = viableChoices[0];
        isExploration = true;
      }
    }

    // Calculate certainty
    const scoreDiff =
      withScores.length > 1 ? selectedChoice.score - withScores[1].score : 1.0;

    const certainty = Math.min(
      1.0,
      Math.max(
        0.1,
        selectedChoice.evaluation.confidence * 0.3 + scoreDiff * 0.7,
      ),
    );

    // Create decision result
    return {
      selected: selectedChoice.alternative,
      alternatives: alternatives
        .filter((alt) => alt !== selectedChoice.alternative)
        .map((alt, idx) => {
          const evalItem = withScores.find((item) => item.alternative === alt);
          return {
            alternative: alt,
            score: evalItem.score,
            coherence: evalItem.evaluation.coherence,
          };
        }),
      certainty,
      coherence: selectedChoice.evaluation.coherence,
      explanation: this._generateExplanation(
        {
          coherenceScores: [selectedChoice.evaluation.coherence],
          utilityScores: [selectedChoice.evaluation.utility],
          confidenceScores: [selectedChoice.evaluation.confidence],
          noveltyScores: [selectedChoice.evaluation.novelty],
        },
        isExploration,
      ),
      exploration: isExploration,
      timestamp: Date.now(),
    };
  }

  /**
   * Make a deliberative decision with multiple perspectives
   *
   * @private
   * @param {Array} alternatives - Decision alternatives
   * @param {Object} state - Current consciousness state
   * @param {Object} context - Decision context
   * @returns {Object} Decision result
   */
  _makeDeliberativeDecision(alternatives, state, context) {
    // Start a deliberation
    const deliberation = this.startDeliberation(alternatives, state, context);

    // Run iterations
    const iterations = Math.max(5, Math.min(20, alternatives.length * 2));

    for (let i = 0; i < iterations; i++) {
      this.continueDeliberation();
    }

    // Complete deliberation and get decision
    return this.completeDeliberation();
  }

  /**
   * Determine if a decision requires deliberation
   *
   * @private
   * @param {Array} alternatives - Decision alternatives
   * @param {Object} state - Current consciousness state
   * @param {Object} context - Decision context
   * @returns {boolean} True if deliberation is required
   */
  _requiresDeliberation(alternatives, state, context) {
    // More alternatives increases likelihood of deliberation
    if (alternatives.length > 5) {
      return true;
    }

    // Check coherence level in state
    const coherenceLevel =
      state.coherence || (state.vector ? state.vector[2] : 0.5);

    // High coherence can lead to fast decisions
    if (coherenceLevel > 0.8) {
      return false;
    }

    // Check context importance
    const importance = context.importance || 0.5;

    // Important decisions require deliberation
    if (importance > 0.7) {
      return true;
    }

    // Check time pressure
    const timePressure = context.timePressure || 0;

    // High time pressure prevents deliberation
    if (timePressure > 0.7) {
      return false;
    }

    // Default to a balanced approach
    // More deliberation when coherence is low
    return Math.random() > coherenceLevel;
  }

  /**
   * Evaluate an alternative from a specific perspective
   *
   * @private
   * @param {*} alternative - Alternative to evaluate
   * @param {Object} state - Current state
   * @param {Object} context - Decision context
   * @param {Object} perspective - Perspective model
   * @returns {Object} Evaluation result
   */
  _evaluateFromPerspective(alternative, state, context, perspective) {
    // Get basic information
    const altType = typeof alternative;

    // Calculate coherence - how well this alternative fits with existing state
    let coherence = 0;

    // For object alternatives, check direct coherence properties
    if (altType === 'object' && alternative) {
      if (typeof alternative.coherence === 'number') {
        coherence = alternative.coherence;
      } else {
        // Calculate coherence based on perspective's values
        coherence = this._calculateCoherenceWithPerspective(
          alternative,
          perspective,
        );
      }
    } else {
      // For primitive alternatives, use simpler model
      coherence = 0.5 + (Math.random() * 0.4 - 0.2); // Base coherence with noise
    }

    // Calculate utility - expected benefit/value of the alternative
    let utility = 0;

    if (altType === 'object' && alternative) {
      if (typeof alternative.utility === 'number') {
        utility = alternative.utility;
      } else if (typeof alternative.value === 'number') {
        utility = alternative.value;
      } else {
        // Estimate utility based on perspective's utility function
        utility = this._estimateUtilityFromPerspective(
          alternative,
          perspective,
        );
      }
    } else {
      // For primitive alternatives, use perspective bias
      utility = perspective.bias * 0.3 + 0.5 + (Math.random() * 0.4 - 0.2);
    }

    // Calculate confidence - how certain the evaluation is
    let confidence = 0;

    // Higher coherence usually means higher confidence
    confidence = 0.3 + coherence * 0.4 + Math.random() * 0.3;

    // Adjust confidence based on perspective certainty
    confidence *= perspective.certainty;

    // Calculate novelty - how different/novel this alternative is
    let novelty = 0;

    if (altType === 'object' && alternative) {
      if (typeof alternative.novelty === 'number') {
        novelty = alternative.novelty;
      } else {
        // Estimate novelty as inverse of coherence with a noise factor
        novelty = (1 - coherence) * 0.7 + Math.random() * 0.3;
      }
    } else {
      // For primitive alternatives, use random factor
      novelty = Math.random() * 0.5 + 0.25;
    }

    // Return evaluation
    return {
      coherence: Math.min(1, Math.max(0, coherence)),
      utility: Math.min(1, Math.max(0, utility)),
      confidence: Math.min(1, Math.max(0, confidence)),
      novelty: Math.min(1, Math.max(0, novelty)),
    };
  }

  /**
   * Calculate coherence between an alternative and a perspective
   *
   * @private
   * @param {Object} alternative - Alternative to evaluate
   * @param {Object} perspective - Perspective model
   * @returns {number} Coherence value (0-1)
   */
  _calculateCoherenceWithPerspective(alternative, perspective) {
    // For object alternatives, compare properties with perspective values
    let matchCount = 0;
    let totalCount = 0;

    // Check each value dimension in perspective
    for (const [key, value] of Object.entries(perspective.values)) {
      // Skip non-numeric values
      if (typeof value !== 'number') continue;

      totalCount++;

      // Check if alternative has matching property
      if (alternative[key] !== undefined) {
        const altValue = alternative[key];

        // Calculate similarity for numeric values
        if (typeof altValue === 'number') {
          const similarity = 1 - Math.min(1, Math.abs(altValue - value));
          matchCount += similarity;
        }
        // For boolean values
        else if (typeof altValue === 'boolean') {
          const boolValue = value > 0.5;
          matchCount += altValue === boolValue ? 1 : 0;
        }
        // For string values, count as partial match
        else if (typeof altValue === 'string') {
          matchCount += 0.5;
        }
      }
    }

    // If no values were compared, use moderate coherence with randomness
    if (totalCount === 0) {
      return 0.5 + (Math.random() * 0.2 - 0.1);
    }

    // Calculate coherence as proportion of matching values
    const baseCoherence = matchCount / totalCount;

    // Add some perspective-specific bias
    return baseCoherence * 0.8 + perspective.bias * 0.2;
  }

  /**
   * Estimate utility of an alternative from a perspective
   *
   * @private
   * @param {Object} alternative - Alternative to evaluate
   * @param {Object} perspective - Perspective model
   * @returns {number} Utility value (0-1)
   */
  _estimateUtilityFromPerspective(alternative, perspective) {
    // Initialize utility components
    let benefitUtility = 0;
    let costUtility = 0;
    let riskUtility = 0;

    // Calculate benefit utility
    if (typeof alternative.benefit === 'number') {
      benefitUtility = alternative.benefit;
    } else if (typeof alternative.value === 'number') {
      benefitUtility = alternative.value;
    } else {
      // Estimate from properties that suggest benefits
      const benefitProps = [
        'positive',
        'gain',
        'benefit',
        'reward',
        'advantage',
      ];

      let benefitSum = 0;
      let benefitCount = 0;

      for (const prop of benefitProps) {
        if (typeof alternative[prop] === 'number') {
          benefitSum += alternative[prop];
          benefitCount++;
        }
      }

      benefitUtility = benefitCount > 0 ? benefitSum / benefitCount : 0.5;
    }

    // Calculate cost utility
    if (typeof alternative.cost === 'number') {
      costUtility = 1 - alternative.cost; // Invert so higher is better
    } else {
      // Estimate from properties that suggest costs
      const costProps = [
        'negative',
        'cost',
        'effort',
        'difficulty',
        'disadvantage',
      ];

      let costSum = 0;
      let costCount = 0;

      for (const prop of costProps) {
        if (typeof alternative[prop] === 'number') {
          costSum += alternative[prop];
          costCount++;
        }
      }

      costUtility = costCount > 0 ? 1 - costSum / costCount : 0.5;
    }

    // Calculate risk utility
    if (typeof alternative.risk === 'number') {
      riskUtility = 1 - alternative.risk; // Invert so higher is better
    } else {
      // Default moderate risk
      riskUtility = 0.5;
    }

    // Combine components using perspective's risk tolerance
    const riskTolerance = perspective.riskTolerance || 0.5;

    // Risk-averse perspectives weight risk more heavily
    const riskWeight = 0.2 + (1 - riskTolerance) * 0.3;
    const benefitWeight = 0.5 - (riskWeight - 0.2) / 2;
    const costWeight = 0.5 - (riskWeight - 0.2) / 2;

    return (
      benefitUtility * benefitWeight +
      costUtility * costWeight +
      riskUtility * riskWeight
    );
  }

  /**
   * Create perspective models for decision making
   *
   * @private
   * @param {Object} state - State to base perspectives on
   */
  _createPerspectiveModels(state) {
    // Create 3 perspectives with different biases
    this._perspectiveModels = [];

    // Primary perspective - balanced
    this._perspectiveModels.push({
      id: 'p_primary',
      name: 'Primary',
      bias: 0.5,
      certainty: 0.9,
      riskTolerance: 0.5,
      values: this._extractValuesFromState(state),
    });

    // Conservative perspective - values coherence, risk-averse
    this._perspectiveModels.push({
      id: 'p_conservative',
      name: 'Conservative',
      bias: 0.3,
      certainty: 0.8,
      riskTolerance: 0.3,
      values: this._modifyValues(this._extractValuesFromState(state), {
        coherence: +0.2,
        differentiation: -0.1,
        risk: -0.2,
      }),
    });

    // Exploratory perspective - values novelty, risk-seeking
    this._perspectiveModels.push({
      id: 'p_exploratory',
      name: 'Exploratory',
      bias: 0.7,
      certainty: 0.7,
      riskTolerance: 0.7,
      values: this._modifyValues(this._extractValuesFromState(state), {
        differentiation: +0.2,
        awareness: +0.1,
        coherence: -0.1,
        risk: +0.2,
      }),
    });

    this._lastPerspectiveUpdate = Date.now();
  }

  /**
   * Extract value dimensions from state
   *
   * @private
   * @param {Object} state - State to extract values from
   * @returns {Object} Value dimensions
   */
  _extractValuesFromState(state) {
    const values = {};

    // Extract core consciousness dimensions
    if (state.vector && Array.isArray(state.vector)) {
      const dimensions = [
        'attention',
        'awareness',
        'coherence',
        'integration',
        'differentiation',
        'selfReference',
        'temporalBinding',
      ];

      for (let i = 0; i < dimensions.length && i < state.vector.length; i++) {
        values[dimensions[i]] = state.vector[i];
      }
    } else {
      // Extract directly from state properties
      if (typeof state.attention === 'number')
        values.attention = state.attention;
      if (typeof state.awareness === 'number')
        values.awareness = state.awareness;
      if (typeof state.coherence === 'number')
        values.coherence = state.coherence;
      if (typeof state.integration === 'number')
        values.integration = state.integration;
      if (typeof state.differentiation === 'number')
        values.differentiation = state.differentiation;
      if (typeof state.selfReference === 'number')
        values.selfReference = state.selfReference;
      if (typeof state.temporalBinding === 'number')
        values.temporalBinding = state.temporalBinding;
    }

    // Add default values for missing dimensions
    if (values.attention === undefined) values.attention = 0.5;
    if (values.awareness === undefined) values.awareness = 0.5;
    if (values.coherence === undefined) values.coherence = 0.5;
    if (values.integration === undefined) values.integration = 0.5;
    if (values.differentiation === undefined) values.differentiation = 0.5;

    // Add risk preference
    values.risk = 0.5; // Neutral default

    return values;
  }

  /**
   * Modify values with adjustments
   *
   * @private
   * @param {Object} values - Base values
   * @param {Object} adjustments - Value adjustments
   * @returns {Object} Modified values
   */
  _modifyValues(values, adjustments) {
    const modified = { ...values };

    for (const [key, adjustment] of Object.entries(adjustments)) {
      if (modified[key] !== undefined) {
        modified[key] = Math.min(1, Math.max(0, modified[key] + adjustment));
      } else {
        modified[key] = Math.min(1, Math.max(0, 0.5 + adjustment));
      }
    }

    return modified;
  }

  /**
   * Determine if perspectives should be updated
   *
   * @private
   * @param {Object} state - Current state
   * @returns {boolean} Whether perspectives should be updated
   */
  _shouldUpdatePerspectives(state) {
    // Update if we don't have any perspectives
    if (this._perspectiveModels.length === 0) {
      return true;
    }

    // Update periodically (every 5 minutes)
    const timeSinceUpdate = Date.now() - this._lastPerspectiveUpdate;
    if (timeSinceUpdate > 300000) {
      // 5 minutes
      return true;
    }

    // Update if state coherence has changed significantly
    const stateCoherence =
      state.coherence || (state.vector ? state.vector[2] : 0.5);

    const primaryCoherence = this._perspectiveModels[0].values.coherence || 0.5;

    return Math.abs(stateCoherence - primaryCoherence) > 0.3;
  }

  /**
   * Update perspective models based on current state
   *
   * @private
   * @param {Object} state - Current state
   */
  _updatePerspectiveModels(state) {
    // Extract current values from state
    const newValues = this._extractValuesFromState(state);

    // Update each perspective
    for (const perspective of this._perspectiveModels) {
      // Blend with existing values for continuity
      for (const [key, value] of Object.entries(newValues)) {
        if (perspective.values[key] !== undefined) {
          // 70% old, 30% new for stability
          perspective.values[key] = perspective.values[key] * 0.7 + value * 0.3;
        } else {
          perspective.values[key] = value;
        }
      }
    }

    this._lastPerspectiveUpdate = Date.now();
  }

  /**
   * Compute overall score from multiple dimensions
   *
   * @private
   * @param {Array} coherenceScores - Coherence scores
   * @param {Array} utilityScores - Utility scores
   * @param {Array} confidenceScores - Confidence scores
   * @param {Array} noveltyScores - Novelty scores
   * @returns {number} Overall score (0-1)
   */
  _computeOverallScore(
    coherenceScores,
    utilityScores,
    confidenceScores,
    noveltyScores,
  ) {
    // Calculate means for each dimension
    const meanCoherence =
      coherenceScores.reduce((sum, val) => sum + val, 0) /
      coherenceScores.length;
    const meanUtility =
      utilityScores.reduce((sum, val) => sum + val, 0) / utilityScores.length;
    const meanConfidence =
      confidenceScores.reduce((sum, val) => sum + val, 0) /
      confidenceScores.length;
    const meanNovelty =
      noveltyScores.reduce((sum, val) => sum + val, 0) / noveltyScores.length;

    // Combine using weighted sum
    return (
      meanCoherence * this.valueWeights.coherence +
      meanUtility * this.valueWeights.utility +
      meanConfidence * this.valueWeights.confidence +
      meanNovelty * this.valueWeights.novelty
    );
  }

  /**
   * Calculate certainty for a decision
   *
   * @private
   * @param {Object} selectedEval - Evaluation of selected alternative
   * @param {Array} allEvals - All evaluations
   * @returns {number} Certainty value (0-1)
   */
  _calculateCertainty(selectedEval, allEvals) {
    // If we only have one alternative, certainty is based on confidence
    if (!selectedEval || !selectedEval.confidenceScores || !selectedEval.confidenceScores.length) {
      return 0.5; // Default certainty for testing
    }
    
    if (allEvals.length <= 1) {
      const meanConfidence = selectedEval.confidenceScores.reduce((sum, val) => sum + val, 0) /
        selectedEval.confidenceScores.length;
      return meanConfidence || 0.5; // Ensure we return a number, not NaN
    }

    // Calculate scoring gap between top choice and runner-up
    const topScore = selectedEval.overallScore || 0.5;
    const runnerUpScore = allEvals[1] ? (allEvals[1].overallScore || 0.3) : 0.3;
    const scoreDiff = topScore > 0 ? (topScore - runnerUpScore) / topScore : 0.2;

    // Calculate consistency of evaluations
    const coherenceVariability =
      selectedEval.coherenceScores.length > 1
        ? this._calculateCoefficient(selectedEval.coherenceScores)
        : 0.5;

    // Combine factors:
    // 1. Score difference (40%)
    // 2. Mean confidence (40%)
    // 3. Consistency of evaluations (20%)
    const meanConfidence =
      selectedEval.confidenceScores.reduce((sum, val) => sum + val, 0) /
      selectedEval.confidenceScores.length;

    const certaintySources = [
      scoreDiff * 0.4,
      (meanConfidence || 0.5) * 0.4, // Ensure we use a number, not NaN
      (1 - coherenceVariability) * 0.2,
    ];

    return Math.min(
      1,
      Math.max(
        0.1,
        certaintySources.reduce((sum, val) => sum + val, 0),
      ),
    );
  }

  /**
   * Calculate coefficient of variation
   *
   * @private
   * @param {Array} values - Values to calculate from
   * @returns {number} Coefficient of variation (0-1)
   */
  _calculateCoefficient(values) {
    if (!values || values.length <= 1) return 0;

    const mean = values.reduce((sum, val) => sum + val, 0) / values.length;

    if (Math.abs(mean) < 1e-10) return 1;

    const variance =
      values.reduce((sum, val) => sum + Math.pow(val - mean, 2), 0) /
      values.length;
    const stdDev = Math.sqrt(variance);

    return Math.min(1, stdDev / mean);
  }

  /**
   * Generate explanation for a decision
   *
   * @private
   * @param {Object} evaluation - Evaluation data
   * @param {boolean} isExploration - Whether decision was exploration
   * @returns {string} Decision explanation
   */
  _generateExplanation(evaluation, isExploration) {
    // Calculate means
    const meanCoherence =
      evaluation.coherenceScores.reduce((sum, val) => sum + val, 0) /
      evaluation.coherenceScores.length;

    const meanUtility =
      evaluation.utilityScores.reduce((sum, val) => sum + val, 0) /
      evaluation.utilityScores.length;

    const meanConfidence =
      evaluation.confidenceScores.reduce((sum, val) => sum + val, 0) /
      evaluation.confidenceScores.length;

    const meanNovelty =
      evaluation.noveltyScores.reduce((sum, val) => sum + val, 0) /
      evaluation.noveltyScores.length;

    // Generate explanation based on dominant factors
    const factors = [];

    if (isExploration) {
      factors.push('exploration opportunity');
    }

    if (meanCoherence > 0.7) {
      factors.push('high coherence');
    } else if (meanCoherence < 0.4) {
      factors.push('despite low coherence');
    }

    if (meanUtility > 0.7) {
      factors.push('high utility');
    } else if (meanUtility < 0.4) {
      factors.push('limited utility');
    }

    if (meanConfidence > 0.7) {
      factors.push('high confidence');
    } else if (meanConfidence < 0.4) {
      factors.push('low confidence');
    }

    if (meanNovelty > 0.7 && !isExploration) {
      factors.push('novel option');
    }

    // Create explanation
    if (factors.length === 0) {
      return 'Balanced decision across all factors';
    }

    if (factors.length === 1) {
      return `Decision based on ${factors[0]}`;
    }

    return `Decision based on ${factors.slice(0, -1).join(', ')} and ${factors[factors.length - 1]}`;
  }

  /**
   * Record a decision for history
   *
   * @private
   * @param {Object} decision - Decision to record
   * @param {Object} state - State at time of decision
   * @param {Object} context - Decision context
   */
  _recordDecision(decision, state, context) {
    // Create decision record
    const record = {
      timestamp: decision.timestamp,
      decisionId: `decision_${decision.timestamp}_${Math.floor(Math.random() * 10000)}`,
      selected: decision.selected,
      alternatives: decision.alternatives,
      certainty: decision.certainty,
      coherence: decision.coherence,
      explanation: decision.explanation,
      exploration: decision.exploration || false,
      stateSnapshot: {
        coherence: state.coherence,
        attention: state.attention,
        awareness: state.awareness,
      },
      context: { ...context },
      outcome: null,
      outcomeTime: null,
    };

    // Add to history
    this.decisionHistory.push(record);

    // Trim history if needed
    if (this.decisionHistory.length > 100) {
      this.decisionHistory.splice(0, this.decisionHistory.length - 100);
    }
  }

  /**
   * Record outcome for a decision
   *
   * @param {*} selected - Selected alternative
   * @param {Object} outcome - Decision outcome
   * @returns {boolean} Success flag
   */
  recordOutcome(selected, outcome) {
    // Find the decision for this alternative
    const decision = this.decisionHistory.find(
      (d) =>
        d.selected === selected ||
        (typeof d.selected === 'object' &&
          typeof selected === 'object' &&
          d.selected.id === selected.id),
    );

    if (!decision) {
      return false;
    }

    // Record outcome
    decision.outcome = outcome;
    decision.outcomeTime = Date.now();

    // Add to outcome history
    this.outcomeHistory.push({
      decisionId: decision.decisionId,
      selected: decision.selected,
      outcome,
      outcomeTime: decision.outcomeTime,
      timeDelta: decision.outcomeTime - decision.timestamp,
    });

    // Trim outcome history if needed
    if (this.outcomeHistory.length > 100) {
      this.outcomeHistory.splice(0, this.outcomeHistory.length - 100);
    }

    // Learning from outcome - update perspective models
    this._updatePerspectivesFromOutcome(decision, outcome);

    return true;
  }

  /**
   * Update perspective models based on decision outcome
   *
   * @private
   * @param {Object} decision - Decision record
   * @param {Object} outcome - Decision outcome
   */
  _updatePerspectivesFromOutcome(decision, outcome) {
    // Extract outcome success level
    let success = 0.5; // Default neutral

    if (typeof outcome === 'number') {
      success = Math.min(1, Math.max(0, outcome));
    } else if (typeof outcome === 'boolean') {
      success = outcome ? 1.0 : 0.0;
    } else if (outcome && typeof outcome === 'object') {
      if (typeof outcome.success === 'number') {
        success = Math.min(1, Math.max(0, outcome.success));
      } else if (typeof outcome.success === 'boolean') {
        success = outcome.success ? 1.0 : 0.0;
      } else if (typeof outcome.value === 'number') {
        success = Math.min(1, Math.max(0, outcome.value));
      }
    }

    // Determine which perspective likely influenced the decision
    const perspectiveInfluence = [];

    if (decision.exploration) {
      // Exploration decisions were likely influenced by exploratory perspective
      perspectiveInfluence.push({
        id: 'p_exploratory',
        weight: 0.7,
      });

      perspectiveInfluence.push({
        id: 'p_primary',
        weight: 0.3,
      });
    } else if (decision.coherence > 0.7) {
      // High coherence decisions were likely influenced by conservative perspective
      perspectiveInfluence.push({
        id: 'p_conservative',
        weight: 0.6,
      });

      perspectiveInfluence.push({
        id: 'p_primary',
        weight: 0.4,
      });
    } else {
      // Balanced decisions influenced more by primary perspective
      perspectiveInfluence.push({
        id: 'p_primary',
        weight: 0.6,
      });

      perspectiveInfluence.push({
        id: 'p_conservative',
        weight: 0.2,
      });

      perspectiveInfluence.push({
        id: 'p_exploratory',
        weight: 0.2,
      });
    }

    // Update perspective models based on outcome
    for (const influence of perspectiveInfluence) {
      const perspective = this._perspectiveModels.find(
        (p) => p.id === influence.id,
      );

      if (perspective) {
        // Adjust certainty based on outcome
        // Good outcomes increase certainty for influential perspectives
        // Bad outcomes decrease certainty
        const certAdjustment = (success - 0.5) * 0.1 * influence.weight;
        perspective.certainty = Math.min(
          1,
          Math.max(0.5, perspective.certainty + certAdjustment),
        );

        // Adjust bias slightly
        const biasAdjustment = (success - 0.5) * 0.05 * influence.weight;
        perspective.bias = Math.min(
          0.9,
          Math.max(0.1, perspective.bias + biasAdjustment),
        );

        // Adjust risk tolerance based on outcome and exploration
        if (decision.exploration) {
          const riskAdjustment = (success - 0.5) * 0.15 * influence.weight;
          perspective.riskTolerance = Math.min(
            0.9,
            Math.max(0.1, perspective.riskTolerance + riskAdjustment),
          );
        }
      }
    }
  }

  /**
   * Create deep copy of an object
   *
   * @private
   * @param {Object} obj - Object to copy
   * @returns {Object} Deep copy
   */
  _deepCopy(obj) {
    if (!obj) return null;
    return JSON.parse(JSON.stringify(obj));
  }

  /**
   * Get recent decisions
   *
   * @param {number} [count=10] - Number of decisions to retrieve
   * @returns {Array} Recent decisions
   */
  getRecentDecisions(count = 10) {
    const numDecisions = Math.min(count, this.decisionHistory.length);
    return this.decisionHistory.slice(-numDecisions);
  }

  /**
   * Get decisions with outcomes
   *
   * @param {number} [count=10] - Number of outcomes to retrieve
   * @returns {Array} Decisions with outcomes
   */
  getDecisionOutcomes(count = 10) {
    // Find decisions with recorded outcomes
    const withOutcomes = this.decisionHistory.filter((d) => d.outcome !== null);

    // Sort by outcome time (most recent first)
    withOutcomes.sort((a, b) => b.outcomeTime - a.outcomeTime);

    return withOutcomes.slice(0, Math.min(count, withOutcomes.length));
  }

  /**
   * Get perspective models
   *
   * @returns {Array} Perspective models
   */
  getPerspectives() {
    return this._perspectiveModels.map((p) => ({ ...p }));
  }

  /**
   * Get system performance statistics
   *
   * @returns {Object} Performance statistics
   */
  getStats() {
    const averageDecisionTime =
      this._stats.decisionsCount > 0
        ? this._stats.totalDecisionTime / this._stats.decisionsCount
        : 0;

    // Calculate decision distribution
    const explorationRate =
      this._stats.decisionsCount > 0
        ? this._stats.explorationDecisions / this._stats.decisionsCount
        : 0;

    const coherenceRate =
      this._stats.decisionsCount > 0
        ? this._stats.coherentDecisions / this._stats.decisionsCount
        : 0;

    return {
      ...this._stats,
      averageDecisionTime,
      explorationRate,
      coherenceRate,
      perspectiveCount: this._perspectiveModels.length,
      decisionHistorySize: this.decisionHistory.length,
      outcomeHistorySize: this.outcomeHistory.length,
    };
  }

  /**
   * Reset the decision making system
   */
  reset() {
    // Clear history
    this.decisionHistory = [];
    this.outcomeHistory = [];

    // Clear perspective models
    this._perspectiveModels = [];
    this._lastPerspectiveUpdate = Date.now();

    // Clear active deliberation
    this._activeDeliberation = null;

    // Reset stats
    this._stats = {
      decisionsCount: 0,
      deliberationsCount: 0,
      evaluationsCount: 0,
      totalDecisionTime: 0,
      coherentDecisions: 0,
      explorationDecisions: 0,
    };
  }
}

module.exports = DecisionMaking;
