/**
 * PrimeOS JavaScript Library - Distributed Coherence Metrics Module
 * Tracking and reporting of coherence metrics
 */

// Import the Prime object from core
const Prime = require("../core");

/**
 * Coherence metrics manager
 * Tracks and analyzes coherence metrics across the system
 */
class CoherenceMetricsManager {
  /**
   * Create a new coherence metrics manager
   * @param {Object} config - Configuration options
   */
  constructor(config = {}) {
    this.metrics = {
      checksPerformed: 0,
      violationsDetected: 0,
      recoveryActions: 0,
      averageCoherenceScore: 1.0,
      minCoherenceScore: 1.0,
      coherenceHistory: [],
      violationsByType: {},
      violationsBySeverity: {},
      recoveryByStrategy: {},
      networkPartitions: {
        detected: 0,
        recovered: 0,
        currentActive: 0,
        timeInPartitionedState: 0,
        lastPartitionTimestamp: null,
      },
    };

    // Initialize violation counters by type
    const violationTypes = Object.values(
      Prime.Distributed.Coherence.Violations.Types,
    );
    violationTypes.forEach((type) => {
      this.metrics.violationsByType[type] = 0;
    });

    // Initialize violation counters by severity
    const severityLevels = Object.values(
      Prime.Distributed.Coherence.Violations.Severity,
    );
    severityLevels.forEach((severity) => {
      this.metrics.violationsBySeverity[severity] = 0;
    });

    // Initialize recovery counters by strategy
    const recoveryStrategies = Object.values(
      Prime.Distributed.Coherence.Recovery.Strategies,
    );
    recoveryStrategies.forEach((strategy) => {
      this.metrics.recoveryByStrategy[strategy] = 0;
    });

    // Configuration
    this.config = {
      historySize: config.historySize || 100,
      reportingInterval: config.reportingInterval || 10,
    };

    // Last report timestamp
    this.lastReportTimestamp = Date.now();
  }

  /**
   * Update metrics with coherence check results
   * @param {number} coherenceScore - Overall coherence score
   * @param {Object} checkResults - Results from checks
   * @param {Object} recoveryActions - Recovery actions taken
   */
  updateMetrics(coherenceScore, checkResults, recoveryActions = null) {
    // Update check counters
    this.metrics.checksPerformed++;

    // Update coherence score tracking
    this.metrics.coherenceHistory.push({
      timestamp: Date.now(),
      score: coherenceScore,
      hasViolations:
        checkResults &&
        checkResults.violations &&
        checkResults.violations.length > 0,
    });

    // Limit history size
    if (this.metrics.coherenceHistory.length > this.config.historySize) {
      this.metrics.coherenceHistory = this.metrics.coherenceHistory.slice(
        -this.config.historySize,
      );
    }

    // Recalculate average coherence score
    const sum = this.metrics.coherenceHistory.reduce(
      (total, entry) => total + entry.score,
      0,
    );
    this.metrics.averageCoherenceScore =
      sum / this.metrics.coherenceHistory.length;

    // Update min coherence score
    this.metrics.minCoherenceScore = Math.min(
      this.metrics.minCoherenceScore,
      coherenceScore,
    );

    // Update violations metrics
    if (checkResults && checkResults.violations) {
      this.metrics.violationsDetected += checkResults.violations.length;

      // Update by type and severity
      for (const violation of checkResults.violations) {
        if (violation.type) {
          this.metrics.violationsByType[violation.type] =
            (this.metrics.violationsByType[violation.type] || 0) + 1;
        }

        if (violation.severity) {
          this.metrics.violationsBySeverity[violation.severity] =
            (this.metrics.violationsBySeverity[violation.severity] || 0) + 1;
        }
      }

      // Check for network partitions
      const networkViolations = checkResults.violations.filter(
        (v) => v.type === Prime.Distributed.Coherence.Violations.Types.NETWORK,
      );

      if (networkViolations.length > 0) {
        // Network partition detected
        if (this.metrics.networkPartitions.currentActive === 0) {
          // New partition detected
          this.metrics.networkPartitions.detected++;
          this.metrics.networkPartitions.lastPartitionTimestamp = Date.now();
        }
        this.metrics.networkPartitions.currentActive = networkViolations.length;
      } else if (this.metrics.networkPartitions.currentActive > 0) {
        // Network partition recovered
        this.metrics.networkPartitions.recovered++;
        this.metrics.networkPartitions.currentActive = 0;

        // Calculate time in partitioned state
        if (this.metrics.networkPartitions.lastPartitionTimestamp) {
          const partitionDuration =
            Date.now() - this.metrics.networkPartitions.lastPartitionTimestamp;
          this.metrics.networkPartitions.timeInPartitionedState +=
            partitionDuration;
          this.metrics.networkPartitions.lastPartitionTimestamp = null;
        }
      }
    }

    // Update recovery metrics
    if (recoveryActions && recoveryActions.actions) {
      this.metrics.recoveryActions += recoveryActions.actions.length;

      // Update by strategy
      for (const action of recoveryActions.actions) {
        if (action.strategy) {
          this.metrics.recoveryByStrategy[action.strategy] =
            (this.metrics.recoveryByStrategy[action.strategy] || 0) + 1;
        }
      }
    }

    // Generate report if interval elapsed
    const now = Date.now();
    if (
      now - this.lastReportTimestamp >=
      this.config.reportingInterval * 1000
    ) {
      this._generateReport();
      this.lastReportTimestamp = now;
    }
  }

  /**
   * Get current metrics snapshot
   * @returns {Object} Metrics snapshot
   */
  getMetricsSnapshot() {
    return {
      ...this.metrics,
      timestamp: Date.now(),
      isPartitioned: this.metrics.networkPartitions.currentActive > 0,
      coherenceHistorySize: this.metrics.coherenceHistory.length,
    };
  }

  /**
   * Calculate coherence trend over the recorded history
   * @param {number} [periods=5] - Number of periods to analyze
   * @returns {Object} Trend analysis
   */
  analyzeCoherenceTrend(periods = 5) {
    const history = this.metrics.coherenceHistory;
    if (history.length < 2) {
      return {
        trend: "stable",
        description: "Insufficient data for trend analysis",
        delta: 0,
        periods: 0,
      };
    }

    // Determine actual number of periods based on history
    const actualPeriods = Math.min(periods, Math.floor(history.length / 2));

    // Split history into periods
    const periodSize = Math.floor(history.length / actualPeriods);
    const periodAverages = [];

    for (let i = 0; i < actualPeriods; i++) {
      const startIdx = history.length - (i + 1) * periodSize;
      const endIdx = history.length - i * periodSize;
      const periodData = history.slice(startIdx, endIdx);

      const periodSum = periodData.reduce((sum, entry) => sum + entry.score, 0);
      const periodAvg = periodSum / periodData.length;

      periodAverages.push(periodAvg);
    }

    // Reverse to get chronological order
    periodAverages.reverse();

    // Calculate overall trend
    const firstAvg = periodAverages[0];
    const lastAvg = periodAverages[periodAverages.length - 1];
    const delta = lastAvg - firstAvg;

    // Determine trend description
    let trend = "stable";
    let description = "Coherence is stable";

    if (delta > 0.05) {
      trend = "improving";
      description = "Coherence is improving significantly";
    } else if (delta > 0.01) {
      trend = "slightly-improving";
      description = "Coherence is slightly improving";
    } else if (delta < -0.05) {
      trend = "degrading";
      description = "Coherence is degrading significantly";
    } else if (delta < -0.01) {
      trend = "slightly-degrading";
      description = "Coherence is slightly degrading";
    }

    return {
      trend,
      description,
      delta,
      periods: actualPeriods,
      periodAverages,
    };
  }

  /**
   * Generate a coherence metrics report
   * @private
   */
  _generateReport() {
    const snapshot = this.getMetricsSnapshot();
    const trend = this.analyzeCoherenceTrend();

    // Create report
    const report = {
      timestamp: Date.now(),
      metrics: snapshot,
      trend,
      summary: {
        coherenceScore: snapshot.averageCoherenceScore.toFixed(3),
        checksPerformed: snapshot.checksPerformed,
        violationsDetected: snapshot.violationsDetected,
        violationRate:
          snapshot.checksPerformed > 0
            ? (snapshot.violationsDetected / snapshot.checksPerformed).toFixed(
                3,
              )
            : 0,
        recoveryRate:
          snapshot.violationsDetected > 0
            ? (snapshot.recoveryActions / snapshot.violationsDetected).toFixed(
                3,
              )
            : 0,
        mostCommonViolationType: this._findMostCommon(
          snapshot.violationsByType,
        ),
        mostCommonRecoveryStrategy: this._findMostCommon(
          snapshot.recoveryByStrategy,
        ),
        networkStatus: snapshot.isPartitioned ? "partitioned" : "healthy",
      },
    };

    // Log report if logger available
    if (Prime.Logger && Prime.Logger.info) {
      Prime.Logger.info("Coherence metrics report", { report });
    } else if (console && console.log) {
      console.log("Coherence metrics report:", report.summary);
    }

    // Emit event if event bus available
    if (Prime.EventBus && Prime.EventBus.emit) {
      Prime.EventBus.emit("coherence:metrics:report", report);
    }

    return report;
  }

  /**
   * Find the most common item in an object counter
   * @private
   * @param {Object} counter - Object with counts by key
   * @returns {string|null} Most common key
   */
  _findMostCommon(counter) {
    let mostCommonKey = null;
    let maxCount = 0;

    for (const [key, count] of Object.entries(counter)) {
      if (count > maxCount) {
        mostCommonKey = key;
        maxCount = count;
      }
    }

    return mostCommonKey;
  }

  /**
   * Reset metrics
   */
  resetMetrics() {
    this.metrics.checksPerformed = 0;
    this.metrics.violationsDetected = 0;
    this.metrics.recoveryActions = 0;
    this.metrics.coherenceHistory = [];
    this.metrics.averageCoherenceScore = 1.0;
    this.metrics.minCoherenceScore = 1.0;

    // Reset violation counters
    Object.keys(this.metrics.violationsByType).forEach((type) => {
      this.metrics.violationsByType[type] = 0;
    });

    Object.keys(this.metrics.violationsBySeverity).forEach((severity) => {
      this.metrics.violationsBySeverity[severity] = 0;
    });

    // Reset recovery counters
    Object.keys(this.metrics.recoveryByStrategy).forEach((strategy) => {
      this.metrics.recoveryByStrategy[strategy] = 0;
    });

    // Reset network partition metrics
    this.metrics.networkPartitions = {
      detected: 0,
      recovered: 0,
      currentActive: 0,
      timeInPartitionedState: 0,
      lastPartitionTimestamp: null,
    };
  }
}

// Add to Prime namespace
Prime.Distributed = Prime.Distributed || {};
Prime.Distributed.Coherence = Prime.Distributed.Coherence || {};
Prime.Distributed.Coherence.Metrics = {
  Manager: CoherenceMetricsManager,
};

module.exports = Prime;
