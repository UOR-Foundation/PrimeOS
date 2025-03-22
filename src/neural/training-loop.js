/**
 * PrimeOS JavaScript Library - Neural Network Training Loop
 * Optimized training loop implementation with memory efficiency and coherence monitoring
 */

// Import the Prime object from core
const Prime = require("../core");

// Create the Neural Training Loop module using IIFE
(function () {
  /**
   * Neural Network Training Loop
   * Manages training process with advanced features like early stopping and learning rate scheduling
   */
  class TrainingLoop {
    /**
     * Create a new training loop for a neural network model
     * @param {Prime.Neural.Model.NeuralModel} model - Neural network model to train
     * @param {Object} [config={}] - Training configuration
     * @param {number} [config.epochs=10] - Number of training epochs
     * @param {number} [config.batchSize=32] - Batch size for training
     * @param {Function} [config.onEpochEnd=null] - Callback function at the end of each epoch
     * @param {Function} [config.onBatchEnd=null] - Callback function at the end of each batch
     * @param {boolean} [config.shuffle=true] - Whether to shuffle data before each epoch
     * @param {Object} [config.earlyStoppingConfig=null] - Early stopping configuration
     * @param {Object} [config.lrSchedulerConfig=null] - Learning rate scheduler configuration
     */
    constructor(model, config = {}) {
      if (!model || typeof model.forward !== 'function' || typeof model.backward !== 'function') {
        throw new Error('Invalid model provided to training loop');
      }
      
      this.model = model;
      
      // Set configuration with defaults
      this.config = {
        epochs: config.epochs || 10,
        batchSize: config.batchSize || 32,
        onEpochEnd: config.onEpochEnd || null,
        onBatchEnd: config.onBatchEnd || null,
        shuffle: config.shuffle !== false,
        earlyStoppingConfig: config.earlyStoppingConfig || null,
        lrSchedulerConfig: config.lrSchedulerConfig || null,
        validationSplit: config.validationSplit || 0,
        validationData: config.validationData || null,
        verbose: config.verbose !== false
      };
      
      // Initialize training state
      this.state = {
        currentEpoch: 0,
        currentBatch: 0,
        totalBatches: 0,
        bestLoss: Infinity,
        bestEpoch: 0,
        history: {
          loss: [],
          metric: [],
          valLoss: [],
          valMetric: [],
          learningRate: [],
          coherence: []
        },
        earlyStoppingPatience: 0,
        running: false,
        aborted: false
      };
      
      // Initialize early stopping if configured
      if (this.config.earlyStoppingConfig) {
        this._initEarlyStopping(this.config.earlyStoppingConfig);
      }
      
      // Initialize learning rate scheduler if configured
      if (this.config.lrSchedulerConfig) {
        this._initLearningRateScheduler(this.config.lrSchedulerConfig);
      }
    }
    
    /**
     * Train the model on the provided data
     * @param {Array|TypedArray} x - Input data
     * @param {Array|TypedArray} y - Target data
     * @param {Object} [options={}] - Additional training options
     * @returns {Object} Training history
     */
    async train(x, y, options = {}) {
      // Merge options with configuration
      const config = { ...this.config, ...options };
      
      // Reset state for new training run
      this._resetState();
      this.state.running = true;
      
      // Prepare validation data if validation split is specified
      let trainX = x;
      let trainY = y;
      let valX = null;
      let valY = null;
      
      if (config.validationData) {
        // Use provided validation data
        [valX, valY] = config.validationData;
      } else if (config.validationSplit > 0) {
        // Split training data for validation
        const splitIndex = Math.floor(x.length * (1 - config.validationSplit));
        trainX = x.slice(0, splitIndex);
        trainY = y.slice(0, splitIndex);
        valX = x.slice(splitIndex);
        valY = y.slice(splitIndex);
      }
      
      // Calculate total batches per epoch
      this.state.totalBatches = Math.ceil(trainX.length / config.batchSize);
      
      // Log training start
      if (config.verbose) {
        console.log(`Training on ${trainX.length} samples, batch size: ${config.batchSize}`);
        if (valX) {
          console.log(`Validation on ${valX.length} samples`);
        }
      }
      
      // Main training loop
      for (let epoch = 0; epoch < config.epochs; epoch++) {
        if (this.state.aborted) {
          break;
        }
        
        this.state.currentEpoch = epoch;
        const epochStartTime = Date.now();
        
        // Shuffle training data if enabled
        if (config.shuffle) {
          [trainX, trainY] = this._shuffleData(trainX, trainY);
        }
        
        // Track epoch metrics
        let epochLoss = 0;
        let epochMetric = null;
        let batchesProcessed = 0;
        
        // Process training data in batches
        for (let batchStart = 0; batchStart < trainX.length; batchStart += config.batchSize) {
          if (this.state.aborted) {
            break;
          }
          
          this.state.currentBatch = Math.floor(batchStart / config.batchSize);
          
          // Get current batch
          const batchEnd = Math.min(batchStart + config.batchSize, trainX.length);
          const batchX = trainX.slice(batchStart, batchEnd);
          const batchY = trainY.slice(batchStart, batchEnd);
          
          // Train on batch
          const batchResult = await this._trainOnBatch(batchX, batchY);
          
          // Update epoch metrics
          epochLoss += batchResult.loss * (batchEnd - batchStart);
          if (batchResult.metric !== null) {
            epochMetric = epochMetric === null ? batchResult.metric * (batchEnd - batchStart) : epochMetric + batchResult.metric * (batchEnd - batchStart);
          }
          
          batchesProcessed++;
          
          // Call batch end callback if provided
          if (typeof config.onBatchEnd === 'function') {
            const batchInfo = {
              epoch,
              batch: this.state.currentBatch,
              loss: batchResult.loss,
              metric: batchResult.metric,
              size: batchEnd - batchStart,
              progress: batchEnd / trainX.length
            };
            
            config.onBatchEnd(batchInfo);
          }
        }
        
        // Calculate epoch average metrics
        epochLoss /= trainX.length;
        if (epochMetric !== null) {
          epochMetric /= trainX.length;
        }
        
        // Run validation if available
        let valLoss = null;
        let valMetric = null;
        
        if (valX && valY) {
          const valResults = await this._validate(valX, valY);
          valLoss = valResults.loss;
          valMetric = valResults.metric;
        }
        
        // Record history
        this.state.history.loss.push(epochLoss);
        this.state.history.metric.push(epochMetric);
        this.state.history.valLoss.push(valLoss);
        this.state.history.valMetric.push(valMetric);
        this.state.history.learningRate.push(this.model.optimizer.learningRate);
        this.state.history.coherence.push(this.model.performance.lastCoherence);
        
        // Calculate epoch time
        const epochTime = (Date.now() - epochStartTime) / 1000;
        
        // Check if this is the best model so far (based on validation loss if available, otherwise training loss)
        const monitorLoss = valLoss !== null ? valLoss : epochLoss;
        if (monitorLoss < this.state.bestLoss) {
          this.state.bestLoss = monitorLoss;
          this.state.bestEpoch = epoch;
          this.state.earlyStoppingPatience = 0;
        } else {
          this.state.earlyStoppingPatience++;
        }
        
        // Apply learning rate scheduling if configured
        if (this.lrScheduler) {
          const newLR = this.lrScheduler(
            epoch, 
            this.model.optimizer.learningRate, 
            { loss: epochLoss, valLoss }
          );
          
          if (newLR !== this.model.optimizer.learningRate) {
            this.model.optimizer.learningRate = newLR;
          }
        }
        
        // Log epoch results if verbose
        if (config.verbose) {
          let logMessage = `Epoch ${epoch + 1}/${config.epochs} - ${epochTime.toFixed(1)}s - loss: ${epochLoss.toFixed(4)}`;
          
          if (epochMetric !== null) {
            logMessage += ` - ${config.metric || 'metric'}: ${epochMetric.toFixed(4)}`;
          }
          
          if (valLoss !== null) {
            logMessage += ` - val_loss: ${valLoss.toFixed(4)}`;
            
            if (valMetric !== null) {
              logMessage += ` - val_${config.metric || 'metric'}: ${valMetric.toFixed(4)}`;
            }
          }
          
          console.log(logMessage);
        }
        
        // Call epoch end callback if provided
        if (typeof config.onEpochEnd === 'function') {
          const epochInfo = {
            epoch,
            loss: epochLoss,
            metric: epochMetric,
            valLoss,
            valMetric,
            learningRate: this.model.optimizer.learningRate,
            coherence: this.model.performance.lastCoherence,
            elapsedTime: epochTime
          };
          
          config.onEpochEnd(epochInfo);
        }
        
        // Check early stopping if configured
        if (this._shouldEarlyStop()) {
          if (config.verbose) {
            console.log(`Early stopping at epoch ${epoch + 1}`);
          }
          break;
        }
      }
      
      this.state.running = false;
      
      // Return training history
      return {
        history: this.state.history,
        bestEpoch: this.state.bestEpoch,
        bestLoss: this.state.bestLoss,
        completed: !this.state.aborted,
        epochs: this.state.currentEpoch + 1
      };
    }
    
    /**
     * Train the model on a single batch
     * @private
     * @param {Array|TypedArray} x - Batch input data
     * @param {Array|TypedArray} y - Batch target data
     * @returns {Object} Batch training results
     */
    async _trainOnBatch(x, y) {
      // Forward pass
      const { output, cache } = this.model.forward(x, { training: true });
      
      // Backward pass
      const { loss, gradients } = this.model.backward(y, output, cache);
      
      // Update parameters
      await this.model.update(gradients);
      
      // Calculate metric if available
      let metricValue = null;
      if (this.model.metric) {
        metricValue = this.model.metric(y, output);
      }
      
      return {
        loss,
        metric: metricValue
      };
    }
    
    /**
     * Validate model on validation data
     * @private
     * @param {Array|TypedArray} x - Validation input data
     * @param {Array|TypedArray} y - Validation target data
     * @returns {Object} Validation results
     */
    async _validate(x, y) {
      // Forward pass only (no training)
      const { output } = this.model.forward(x, { training: false });
      
      // Calculate loss
      let loss = 0;
      
      // Use model's loss function
      if (typeof this.model.lossFunction === 'function') {
        const result = this.model.lossFunction(y, output, false);
        loss = result.loss;
      }
      
      // Calculate metric if available
      let metricValue = null;
      if (this.model.metric) {
        metricValue = this.model.metric(y, output);
      }
      
      return {
        loss,
        metric: metricValue
      };
    }
    
    /**
     * Shuffle training data
     * @private
     * @param {Array|TypedArray} x - Input data
     * @param {Array|TypedArray} y - Target data
     * @returns {Array} Shuffled data arrays [x, y]
     */
    _shuffleData(x, y) {
      // Create index array and shuffle it
      const indices = Array.from({ length: x.length }, (_, i) => i);
      
      // Fisher-Yates shuffle
      for (let i = indices.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [indices[i], indices[j]] = [indices[j], indices[i]];
      }
      
      // Create new arrays with shuffled data
      const shuffledX = Array.isArray(x) ? [] : (x instanceof Float32Array ? new Float32Array(x.length) : new Float64Array(x.length));
      const shuffledY = Array.isArray(y) ? [] : (y instanceof Float32Array ? new Float32Array(y.length) : new Float64Array(y.length));
      
      for (let i = 0; i < indices.length; i++) {
        const idx = indices[i];
        
        if (Array.isArray(shuffledX)) {
          shuffledX[i] = x[idx];
        } else {
          shuffledX[i] = x[idx];
        }
        
        if (Array.isArray(shuffledY)) {
          shuffledY[i] = y[idx];
        } else {
          shuffledY[i] = y[idx];
        }
      }
      
      return [shuffledX, shuffledY];
    }
    
    /**
     * Initialize early stopping
     * @private
     * @param {Object} config - Early stopping configuration
     */
    _initEarlyStopping(config) {
      this.earlyStoppingConfig = {
        patience: config.patience || 10,
        minDelta: config.minDelta || 0.001,
        monitor: config.monitor || 'val_loss',
        ...config
      };
    }
    
    /**
     * Check if training should stop early
     * @private
     * @returns {boolean} Whether to stop training
     */
    _shouldEarlyStop() {
      if (!this.earlyStoppingConfig) {
        return false;
      }
      
      return this.state.earlyStoppingPatience >= this.earlyStoppingConfig.patience;
    }
    
    /**
     * Initialize learning rate scheduler
     * @private
     * @param {Object} config - Learning rate scheduler configuration
     */
    _initLearningRateScheduler(config) {
      // Initialize based on scheduler type
      const type = (config.type || 'step').toLowerCase();
      
      switch (type) {
        case 'step':
          // Step decay: reduce learning rate by factor after specified epochs
          this.lrScheduler = (epoch, currentLR, metrics) => {
            const stepSize = config.stepSize || 5;
            const factor = config.factor || 0.1;
            
            if ((epoch + 1) % stepSize === 0) {
              return currentLR * factor;
            }
            return currentLR;
          };
          break;
          
        case 'exponential':
          // Exponential decay: lr = initial_lr * decay^epoch
          this.lrScheduler = (epoch, currentLR, metrics) => {
            const initialLR = config.initialLR || currentLR;
            const decay = config.decay || 0.96;
            
            return initialLR * Math.pow(decay, epoch);
          };
          break;
          
        case 'plateau':
          // Reduce on plateau: reduce when metric stops improving
          this.plateauConfig = {
            patience: config.patience || 5,
            factor: config.factor || 0.5,
            minLR: config.minLR || 1e-6,
            monitor: config.monitor || 'val_loss',
            minDelta: config.minDelta || 0.001,
            cooldown: config.cooldown || 0,
            bestValue: null,
            wait: 0,
            cooldownCounter: 0
          };
          
          this.lrScheduler = (epoch, currentLR, metrics) => {
            const monitor = this.plateauConfig.monitor === 'val_loss' ? 
              metrics.valLoss : metrics.loss;
              
            // Skip if monitor value is null or cooldown is active
            if (monitor === null || this.plateauConfig.cooldownCounter > 0) {
              if (this.plateauConfig.cooldownCounter > 0) {
                this.plateauConfig.cooldownCounter--;
              }
              return currentLR;
            }
            
            // Initialize best value if needed
            if (this.plateauConfig.bestValue === null) {
              this.plateauConfig.bestValue = monitor;
              return currentLR;
            }
            
            // Check if monitor improved
            if (monitor < this.plateauConfig.bestValue - this.plateauConfig.minDelta) {
              this.plateauConfig.bestValue = monitor;
              this.plateauConfig.wait = 0;
              return currentLR;
            } else {
              this.plateauConfig.wait++;
              
              // Reduce learning rate if patience is exhausted
              if (this.plateauConfig.wait >= this.plateauConfig.patience) {
                const newLR = Math.max(currentLR * this.plateauConfig.factor, this.plateauConfig.minLR);
                this.plateauConfig.wait = 0;
                this.plateauConfig.cooldownCounter = this.plateauConfig.cooldown;
                return newLR;
              }
            }
            
            return currentLR;
          };
          break;
          
        case 'cosine':
          // Cosine annealing: smoothly decrease learning rate
          this.lrScheduler = (epoch, currentLR, metrics) => {
            const initialLR = config.initialLR || currentLR;
            const minLR = config.minLR || 0;
            const totalEpochs = config.totalEpochs || this.config.epochs;
            
            return minLR + 0.5 * (initialLR - minLR) * (1 + Math.cos(Math.PI * epoch / totalEpochs));
          };
          break;
          
        case 'custom':
          // Custom scheduler function provided by user
          if (typeof config.scheduler !== 'function') {
            throw new Error('Custom learning rate scheduler requires a scheduler function');
          }
          this.lrScheduler = config.scheduler;
          break;
          
        default:
          throw new Error(`Unknown learning rate scheduler type: ${type}`);
      }
    }
    
    /**
     * Reset training state
     * @private
     */
    _resetState() {
      this.state = {
        currentEpoch: 0,
        currentBatch: 0,
        totalBatches: 0,
        bestLoss: Infinity,
        bestEpoch: 0,
        history: {
          loss: [],
          metric: [],
          valLoss: [],
          valMetric: [],
          learningRate: [],
          coherence: []
        },
        earlyStoppingPatience: 0,
        running: false,
        aborted: false
      };
    }
    
    /**
     * Stop training
     */
    stop() {
      if (this.state.running) {
        this.state.aborted = true;
      }
    }
    
    /**
     * Get training history
     * @returns {Object} Training history
     */
    getHistory() {
      return { ...this.state.history };
    }
    
    /**
     * Get current training state
     * @returns {Object} Current training state
     */
    getState() {
      return {
        currentEpoch: this.state.currentEpoch,
        currentBatch: this.state.currentBatch,
        totalBatches: this.state.totalBatches,
        bestLoss: this.state.bestLoss,
        bestEpoch: this.state.bestEpoch,
        running: this.state.running,
        aborted: this.state.aborted
      };
    }
  }
  
  // Add to Prime.Neural namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Model = Prime.Neural.Model || {};
  Prime.Neural.Model.TrainingLoop = TrainingLoop;
})();

// Export the enhanced Prime object
module.exports = Prime;