/**
 * PrimeOS JavaScript Library - Recurrent Neural Layer Module
 * Advanced recurrent layer implementation with coherence integration
 */

// Import the Prime object from core
const Prime = require('../../core');

// Create the Recurrent Layer module using IIFE
(function () {
  /**
   * Recurrent Neural Layer class
   * Implements gated recurrent units with coherence monitoring
   */
  class RecurrentLayer {
    /**
     * Create a new recurrent layer
     * @param {Object} config - Layer configuration
     * @param {number} config.inputSize - Size of input features
     * @param {number} config.hiddenSize - Size of hidden state
     * @param {string} [config.cellType='gru'] - Type of recurrent cell ('lstm', 'gru', 'simple')
     * @param {number} [config.sequenceLength=1] - Maximum sequence length
     * @param {boolean} [config.returnSequences=false] - Whether to return full sequence or just final state
     * @param {Object} [config.initParams={}] - Weight initialization parameters
     */
    constructor(config) {
      if (!Prime.Utils.isObject(config)) {
        throw new Prime.ValidationError(
          'Layer configuration must be an object',
        );
      }

      this.inputSize = config.inputSize;
      this.hiddenSize = config.hiddenSize;
      this.cellType = config.cellType || 'gru';
      this.sequenceLength = config.sequenceLength || 1;
      this.returnSequences = config.returnSequences || false;

      // Calculate output size based on configuration
      this.outputSize = this.returnSequences
        ? this.sequenceLength * this.hiddenSize
        : this.hiddenSize;

      // Initialize weights and biases for different gate types
      this._initializeParameters(config.initParams || {});

      // Performance tracking
      this.metrics = {
        forwardCount: 0,
        backwardCount: 0,
        averageForwardTime: 0,
        averageBackwardTime: 0,
        coherence: 1.0,
        temporalCoherence: 1.0,
        gradientNorm: 0,
      };

      // Usage pattern tracking
      this.usagePatterns = {
        hiddenStateDistribution: new Array(this.hiddenSize).fill(0),
        gateActivationStatistics: {
          input: new Array(this.hiddenSize).fill(0.5),
          forget: new Array(this.hiddenSize).fill(0.5),
          output: new Array(this.hiddenSize).fill(0.5),
          update: new Array(this.hiddenSize).fill(0.5),
          reset: new Array(this.hiddenSize).fill(0.5),
        },
        temporalDependencies: [], // Track how much current output depends on past inputs
        sampleCount: 0,
      };

      // Coherence validation helpers
      this.validationResults = {
        lastCoherenceScore: 1.0,
        violationHistory: [],
        highestGradientNorm: 0,
      };
    }

    /**
     * Initialize weights and biases for the recurrent layer
     * @private
     * @param {Object} params - Initialization parameters
     */
    _initializeParameters(params) {
      const scale =
        params.scale || Math.sqrt(2 / (this.inputSize + this.hiddenSize));
      const distribution = params.distribution || 'xavier';

      this.weights = {};
      this.biases = {};

      if (this.cellType === 'lstm') {
        // LSTM weights: input gate, forget gate, cell gate, output gate
        // Input weights (applied to input)
        this.weights.Wi = this._initializeMatrix(
          this.hiddenSize,
          this.inputSize,
          scale,
          distribution,
        );
        this.weights.Wf = this._initializeMatrix(
          this.hiddenSize,
          this.inputSize,
          scale,
          distribution,
        );
        this.weights.Wc = this._initializeMatrix(
          this.hiddenSize,
          this.inputSize,
          scale,
          distribution,
        );
        this.weights.Wo = this._initializeMatrix(
          this.hiddenSize,
          this.inputSize,
          scale,
          distribution,
        );

        // Recurrent weights (applied to previous hidden state)
        this.weights.Ui = this._initializeMatrix(
          this.hiddenSize,
          this.hiddenSize,
          scale,
          distribution,
        );
        this.weights.Uf = this._initializeMatrix(
          this.hiddenSize,
          this.hiddenSize,
          scale,
          distribution,
        );
        this.weights.Uc = this._initializeMatrix(
          this.hiddenSize,
          this.hiddenSize,
          scale,
          distribution,
        );
        this.weights.Uo = this._initializeMatrix(
          this.hiddenSize,
          this.hiddenSize,
          scale,
          distribution,
        );

        // Biases
        this.biases.bi = new Array(this.hiddenSize).fill(0);
        this.biases.bf = new Array(this.hiddenSize).fill(1); // Initial bias for forget gate is 1 (remember by default)
        this.biases.bc = new Array(this.hiddenSize).fill(0);
        this.biases.bo = new Array(this.hiddenSize).fill(0);
      } else if (this.cellType === 'gru') {
        // GRU weights: update gate, reset gate, hidden state
        // Input weights
        this.weights.Wz = this._initializeMatrix(
          this.hiddenSize,
          this.inputSize,
          scale,
          distribution,
        );
        this.weights.Wr = this._initializeMatrix(
          this.hiddenSize,
          this.inputSize,
          scale,
          distribution,
        );
        this.weights.Wh = this._initializeMatrix(
          this.hiddenSize,
          this.inputSize,
          scale,
          distribution,
        );

        // Recurrent weights
        this.weights.Uz = this._initializeMatrix(
          this.hiddenSize,
          this.hiddenSize,
          scale,
          distribution,
        );
        this.weights.Ur = this._initializeMatrix(
          this.hiddenSize,
          this.hiddenSize,
          scale,
          distribution,
        );
        this.weights.Uh = this._initializeMatrix(
          this.hiddenSize,
          this.hiddenSize,
          scale,
          distribution,
        );

        // Biases
        this.biases.bz = new Array(this.hiddenSize).fill(0);
        this.biases.br = new Array(this.hiddenSize).fill(0);
        this.biases.bh = new Array(this.hiddenSize).fill(0);
      } else {
        // Simple RNN
        this.weights.Wx = this._initializeMatrix(
          this.hiddenSize,
          this.inputSize,
          scale,
          distribution,
        );
        this.weights.Wh = this._initializeMatrix(
          this.hiddenSize,
          this.hiddenSize,
          scale,
          distribution,
        );
        this.biases.b = new Array(this.hiddenSize).fill(0);
      }
    }

    /**
     * Initialize a weight matrix with appropriate distribution
     * @private
     * @param {number} rows - Number of rows
     * @param {number} cols - Number of columns
     * @param {number} scale - Scale factor for initialization
     * @param {string} distribution - Distribution type ('xavier', 'he', etc.)
     * @returns {Array<Array<number>>} Initialized weight matrix
     */
    _initializeMatrix(rows, cols, scale, distribution) {
      const matrix = new Array(rows);

      for (let i = 0; i < rows; i++) {
        matrix[i] = new Array(cols);

        for (let j = 0; j < cols; j++) {
          let value;

          if (distribution === 'xavier') {
            // Xavier/Glorot initialization
            value = (Math.random() * 2 - 1) * scale;
          } else if (distribution === 'he') {
            // He initialization
            value = Math.random() * Math.sqrt(2 / cols);
          } else if (distribution === 'orthogonal') {
            // Pseudo-orthogonal (simplified for JavaScript)
            value = (Math.random() * 2 - 1) * Math.sqrt(2 / (rows + cols));
          } else if (distribution === 'zeros') {
            value = 0;
          } else {
            // Default to small random values
            value = Math.random() * 0.2 - 0.1;
          }

          matrix[i][j] = value;
        }
      }

      return matrix;
    }

    /**
     * Matrix multiplication
     * @private
     * @param {Array<Array<number>>} a - First matrix
     * @param {Array<number>} b - Vector
     * @returns {Array<number>} Result vector
     */
    _matrixVectorProduct(a, b) {
      const result = new Array(a.length).fill(0);

      for (let i = 0; i < a.length; i++) {
        for (let j = 0; j < b.length; j++) {
          result[i] += a[i][j] * b[j];
        }
      }

      return result;
    }

    /**
     * Element-wise vector addition
     * @private
     * @param {Array<number>} a - First vector
     * @param {Array<number>} b - Second vector
     * @returns {Array<number>} Result vector
     */
    _vectorAdd(a, b) {
      const result = new Array(a.length);

      for (let i = 0; i < a.length; i++) {
        result[i] = a[i] + b[i];
      }

      return result;
    }

    /**
     * Element-wise vector multiplication
     * @private
     * @param {Array<number>} a - First vector
     * @param {Array<number>} b - Second vector
     * @returns {Array<number>} Result vector
     */
    _vectorMultiply(a, b) {
      const result = new Array(a.length);

      for (let i = 0; i < a.length; i++) {
        result[i] = a[i] * b[i];
      }

      return result;
    }

    /**
     * Element-wise vector subtraction (a - b)
     * @private
     * @param {Array<number>} a - First vector
     * @param {Array<number>} b - Second vector
     * @returns {Array<number>} Result vector
     */
    _vectorSubtract(a, b) {
      const result = new Array(a.length);

      for (let i = 0; i < a.length; i++) {
        result[i] = a[i] - b[i];
      }

      return result;
    }

    /**
     * Element-wise sigmoid activation
     * @private
     * @param {Array<number>} x - Input vector
     * @returns {Array<number>} Activated vector
     */
    _sigmoid(x) {
      return x.map((val) => 1 / (1 + Math.exp(-val)));
    }

    /**
     * Element-wise tanh activation
     * @private
     * @param {Array<number>} x - Input vector
     * @returns {Array<number>} Activated vector
     */
    _tanh(x) {
      return x.map((val) => Math.tanh(val));
    }

    /**
     * Element-wise sigmoid derivative
     * @private
     * @param {Array<number>} x - Sigmoid output values
     * @returns {Array<number>} Derivatives
     */
    _sigmoidDerivative(x) {
      return x.map((val) => val * (1 - val));
    }

    /**
     * Element-wise tanh derivative
     * @private
     * @param {Array<number>} x - Tanh output values
     * @returns {Array<number>} Derivatives
     */
    _tanhDerivative(x) {
      return x.map((val) => 1 - val * val);
    }

    /**
     * Vector deep clone
     * @private
     * @param {Array} vector - Vector to clone
     * @returns {Array} Cloned vector
     */
    _cloneVector(vector) {
      return [...vector];
    }

    /**
     * Deep clone a matrix or nested structure
     * @private
     * @param {Array} structure - Structure to clone
     * @returns {Array} Cloned structure
     */
    _deepClone(structure) {
      return JSON.parse(JSON.stringify(structure));
    }

    /**
     * Forward pass for LSTM cell
     * @private
     * @param {Array<number>} x - Input at current time step
     * @param {Array<number>} prevH - Previous hidden state
     * @param {Array<number>} prevC - Previous cell state
     * @returns {Object} Current states and intermediate values
     */
    _forwardLSTM(x, prevH, prevC) {
      // Input gate: decide what information to add to cell state
      const inputGate = this._sigmoid(
        this._vectorAdd(
          this._vectorAdd(
            this._matrixVectorProduct(this.weights.Wi, x),
            this._matrixVectorProduct(this.weights.Ui, prevH),
          ),
          this.biases.bi,
        ),
      );

      // Forget gate: decide what information to throw away from cell state
      const forgetGate = this._sigmoid(
        this._vectorAdd(
          this._vectorAdd(
            this._matrixVectorProduct(this.weights.Wf, x),
            this._matrixVectorProduct(this.weights.Uf, prevH),
          ),
          this.biases.bf,
        ),
      );

      // Cell candidate: create vector of new candidate values
      const cellCandidate = this._tanh(
        this._vectorAdd(
          this._vectorAdd(
            this._matrixVectorProduct(this.weights.Wc, x),
            this._matrixVectorProduct(this.weights.Uc, prevH),
          ),
          this.biases.bc,
        ),
      );

      // Output gate: decide what parts of cell state to output
      const outputGate = this._sigmoid(
        this._vectorAdd(
          this._vectorAdd(
            this._matrixVectorProduct(this.weights.Wo, x),
            this._matrixVectorProduct(this.weights.Uo, prevH),
          ),
          this.biases.bo,
        ),
      );

      // Update cell state: forget old state + add new info
      const cellState = this._vectorAdd(
        this._vectorMultiply(forgetGate, prevC),
        this._vectorMultiply(inputGate, cellCandidate),
      );

      // Update hidden state
      const hiddenState = this._vectorMultiply(
        outputGate,
        this._tanh(cellState),
      );

      // Update gate activation statistics for coherence monitoring
      this._updateGateActivationStatistics({
        input: inputGate,
        forget: forgetGate,
        output: outputGate,
      });

      // Monitor cell state changes for potential issues (exploding/vanishing gradients)
      this._monitorCellStateCoherence(prevC, cellState, inputGate, forgetGate);

      return {
        h: hiddenState,
        c: cellState,
        gates: {
          inputGate,
          forgetGate,
          cellCandidate,
          outputGate,
        },
      };
    }

    /**
     * Forward pass for GRU cell
     * @private
     * @param {Array<number>} x - Input at current time step
     * @param {Array<number>} prevH - Previous hidden state
     * @returns {Object} Current states and intermediate values
     */
    _forwardGRU(x, prevH) {
      // Update gate: decides how much of past info to keep
      const updateGate = this._sigmoid(
        this._vectorAdd(
          this._vectorAdd(
            this._matrixVectorProduct(this.weights.Wz, x),
            this._matrixVectorProduct(this.weights.Uz, prevH),
          ),
          this.biases.bz,
        ),
      );

      // Reset gate: decides how much of past info to forget
      const resetGate = this._sigmoid(
        this._vectorAdd(
          this._vectorAdd(
            this._matrixVectorProduct(this.weights.Wr, x),
            this._matrixVectorProduct(this.weights.Ur, prevH),
          ),
          this.biases.br,
        ),
      );

      // Candidate hidden state
      const resetHidden = this._vectorMultiply(resetGate, prevH);

      const candidateH = this._tanh(
        this._vectorAdd(
          this._vectorAdd(
            this._matrixVectorProduct(this.weights.Wh, x),
            this._matrixVectorProduct(this.weights.Uh, resetHidden),
          ),
          this.biases.bh,
        ),
      );

      // Final hidden state: combination of previous and candidate
      const hiddenState = this._vectorAdd(
        this._vectorMultiply(updateGate, prevH),
        this._vectorMultiply(
          this._vectorSubtract(
            new Array(updateGate.length).fill(1),
            updateGate,
          ),
          candidateH,
        ),
      );

      // Update gate activation statistics for coherence monitoring
      this._updateGateActivationStatistics({
        update: updateGate,
        reset: resetGate,
      });

      return {
        h: hiddenState,
        gates: {
          updateGate,
          resetGate,
          candidateH,
        },
      };
    }

    /**
     * Forward pass for Simple RNN cell
     * @private
     * @param {Array<number>} x - Input at current time step
     * @param {Array<number>} prevH - Previous hidden state
     * @returns {Object} Current states and intermediate values
     */
    _forwardSimpleRNN(x, prevH) {
      // Simple RNN: h_t = tanh(W_x * x_t + W_h * h_{t-1} + b)
      const hiddenState = this._tanh(
        this._vectorAdd(
          this._vectorAdd(
            this._matrixVectorProduct(this.weights.Wx, x),
            this._matrixVectorProduct(this.weights.Wh, prevH),
          ),
          this.biases.b,
        ),
      );

      return {
        h: hiddenState,
      };
    }

    /**
     * Forward pass through the recurrent layer
     * @param {Array<Array<number>>} input - Sequence of input vectors
     * @returns {Object} Output with activation and cache for backprop
     */
    forward(input) {
      const startTime = performance.now();

      // Validate input shape
      if (!Array.isArray(input)) {
        throw new Prime.ValidationError('Input must be an array');
      }

      // Handle both single sample and sequence inputs
      const isSequence = Array.isArray(input[0]);
      let sequence;

      if (!isSequence) {
        // Single time step - convert to sequence of length 1
        sequence = [input];
      } else {
        sequence = input;
      }

      // Ensure sequence has consistent dimensions
      for (let i = 0; i < sequence.length; i++) {
        if (
          !Array.isArray(sequence[i]) ||
          sequence[i].length !== this.inputSize
        ) {
          throw new Prime.ValidationError(
            `Input at time step ${i} must be an array of length ${this.inputSize}`,
          );
        }
      }

      // Initialize states
      const hiddenStates = new Array(sequence.length + 1);
      const cellStates =
        this.cellType === 'lstm' ? new Array(sequence.length + 1) : null;
      const gateStates = new Array(sequence.length);

      // Initial states are zero vectors
      hiddenStates[0] = new Array(this.hiddenSize).fill(0);
      if (cellStates) {
        cellStates[0] = new Array(this.hiddenSize).fill(0);
      }

      // Forward pass through the sequence
      for (let t = 0; t < sequence.length; t++) {
        const x = sequence[t];

        let result;
        if (this.cellType === 'lstm') {
          result = this._forwardLSTM(x, hiddenStates[t], cellStates[t]);
          hiddenStates[t + 1] = result.h;
          cellStates[t + 1] = result.c;
        } else if (this.cellType === 'gru') {
          result = this._forwardGRU(x, hiddenStates[t]);
          hiddenStates[t + 1] = result.h;
        } else {
          result = this._forwardSimpleRNN(x, hiddenStates[t]);
          hiddenStates[t + 1] = result.h;
        }

        gateStates[t] = result.gates || {};
      }

      // Prepare output based on configuration
      let activation;
      if (this.returnSequences) {
        // Return full sequence of hidden states
        activation = hiddenStates.slice(1); // Skip initial state
      } else {
        // Return only final hidden state
        activation = hiddenStates[sequence.length];
      }

      // Update hidden state distribution for coherence tracking
      this._updateHiddenStateDistribution(hiddenStates);

      // Calculate temporal dependencies
      this._updateTemporalDependencies(hiddenStates);

      // Update performance metrics
      const endTime = performance.now();
      this._updateForwardMetrics(endTime - startTime);

      // Cache all intermediate states for backprop
      const cache = {
        sequence,
        hiddenStates,
        cellStates,
        gateStates,
      };

      return {
        activation,
        cache,
      };
    }

    /**
     * Backward pass for LSTM cell
     * @private
     * @param {Array<number>} dh - Gradient of loss w.r.t. hidden state
     * @param {Array<number>} dc - Gradient of loss w.r.t. cell state
     * @param {Array<number>} x - Input at this time step
     * @param {Object} states - States from forward pass
     * @returns {Object} Gradients for input, previous states, and parameters
     */
    _backwardLSTM(dh, dc, x, states) {
      const { prevH, prevC, h, c, gates } = states;
      const { inputGate, forgetGate, cellCandidate, outputGate } = gates;

      // Gradient w.r.t. output gate
      const tanhC = this._tanh(c);
      const dOutputGate = this._vectorMultiply(dh, tanhC);

      // Gradient w.r.t. cell state
      const dTanhC = this._vectorMultiply(dh, outputGate);
      const dTanhCDerivative = this._vectorMultiply(
        dTanhC,
        this._tanhDerivative(tanhC),
      );

      // Add incoming gradient from next time step
      const dCellState = this._vectorAdd(dTanhCDerivative, dc);

      // Gradient w.r.t. forget gate
      const dForgetGate = this._vectorMultiply(dCellState, prevC);

      // Gradient w.r.t. input gate
      const dInputGate = this._vectorMultiply(dCellState, cellCandidate);

      // Gradient w.r.t. cell candidate
      const dCellCandidate = this._vectorMultiply(dCellState, inputGate);

      // Gradient w.r.t. previous cell state
      const dPrevC = this._vectorMultiply(dCellState, forgetGate);

      // Gradients for gate activations
      const dInputGatePre = this._vectorMultiply(
        dInputGate,
        this._sigmoidDerivative(inputGate),
      );

      const dForgetGatePre = this._vectorMultiply(
        dForgetGate,
        this._sigmoidDerivative(forgetGate),
      );

      const dOutputGatePre = this._vectorMultiply(
        dOutputGate,
        this._sigmoidDerivative(outputGate),
      );

      const dCellCandidatePre = this._vectorMultiply(
        dCellCandidate,
        this._tanhDerivative(cellCandidate),
      );

      // Gradients for weights and biases
      const dWi = this._outerProduct(dInputGatePre, x);
      const dWf = this._outerProduct(dForgetGatePre, x);
      const dWc = this._outerProduct(dCellCandidatePre, x);
      const dWo = this._outerProduct(dOutputGatePre, x);

      const dUi = this._outerProduct(dInputGatePre, prevH);
      const dUf = this._outerProduct(dForgetGatePre, prevH);
      const dUc = this._outerProduct(dCellCandidatePre, prevH);
      const dUo = this._outerProduct(dOutputGatePre, prevH);

      const dBi = dInputGatePre;
      const dBf = dForgetGatePre;
      const dBc = dCellCandidatePre;
      const dBo = dOutputGatePre;

      // Gradient w.r.t. input
      const dX = this._vectorAdd(
        this._vectorAdd(
          this._matrixVectorProduct(
            this._transpose(this.weights.Wi),
            dInputGatePre,
          ),
          this._matrixVectorProduct(
            this._transpose(this.weights.Wf),
            dForgetGatePre,
          ),
        ),
        this._vectorAdd(
          this._matrixVectorProduct(
            this._transpose(this.weights.Wc),
            dCellCandidatePre,
          ),
          this._matrixVectorProduct(
            this._transpose(this.weights.Wo),
            dOutputGatePre,
          ),
        ),
      );

      // Gradient w.r.t. previous hidden state
      const dPrevH = this._vectorAdd(
        this._vectorAdd(
          this._matrixVectorProduct(
            this._transpose(this.weights.Ui),
            dInputGatePre,
          ),
          this._matrixVectorProduct(
            this._transpose(this.weights.Uf),
            dForgetGatePre,
          ),
        ),
        this._vectorAdd(
          this._matrixVectorProduct(
            this._transpose(this.weights.Uc),
            dCellCandidatePre,
          ),
          this._matrixVectorProduct(
            this._transpose(this.weights.Uo),
            dOutputGatePre,
          ),
        ),
      );

      // Collect weight and bias gradients
      const dWeights = {
        Wi: dWi,
        Wf: dWf,
        Wc: dWc,
        Wo: dWo,
        Ui: dUi,
        Uf: dUf,
        Uc: dUc,
        Uo: dUo,
      };

      const dBiases = {
        bi: dBi,
        bf: dBf,
        bc: dBc,
        bo: dBo,
      };

      return {
        dX,
        dPrevH,
        dPrevC,
        dWeights,
        dBiases,
      };
    }

    /**
     * Backward pass for GRU cell
     * @private
     * @param {Array<number>} dh - Gradient of loss w.r.t. hidden state
     * @param {Array<number>} x - Input at this time step
     * @param {Object} states - States from forward pass
     * @returns {Object} Gradients for input, previous states, and parameters
     */
    _backwardGRU(dh, x, states) {
      const { prevH, gates } = states;
      const { updateGate, resetGate, candidateH } = gates;

      // Helper: 1 - update
      const oneMinusUpdate = this._vectorSubtract(
        new Array(updateGate.length).fill(1),
        updateGate,
      );

      // Gradient w.r.t. candidate hidden state
      const dCandidateH = this._vectorMultiply(dh, oneMinusUpdate);

      // Gradient w.r.t. update gate
      const dUpdateGate = this._vectorMultiply(
        dh,
        this._vectorSubtract(prevH, candidateH),
      );

      // Gradients for gate activations
      const dUpdateGatePre = this._vectorMultiply(
        dUpdateGate,
        this._sigmoidDerivative(updateGate),
      );

      // Gradient w.r.t. candidate pre-activation
      const dCandidateHPre = this._vectorMultiply(
        dCandidateH,
        this._tanhDerivative(candidateH),
      );

      // Gradient w.r.t. reset gate
      const resetHidden = this._vectorMultiply(resetGate, prevH);

      const dResetHidden = this._matrixVectorProduct(
        this._transpose(this.weights.Uh),
        dCandidateHPre,
      );

      const dResetGate = this._vectorMultiply(dResetHidden, prevH);

      const dResetGatePre = this._vectorMultiply(
        dResetGate,
        this._sigmoidDerivative(resetGate),
      );

      // Gradients for weights and biases
      const dWz = this._outerProduct(dUpdateGatePre, x);
      const dWr = this._outerProduct(dResetGatePre, x);
      const dWh = this._outerProduct(dCandidateHPre, x);

      const dUz = this._outerProduct(dUpdateGatePre, prevH);
      const dUr = this._outerProduct(dResetGatePre, prevH);
      const dUh = this._outerProduct(dCandidateHPre, resetHidden);

      const dBz = dUpdateGatePre;
      const dBr = dResetGatePre;
      const dBh = dCandidateHPre;

      // Gradient w.r.t. input
      const dX = this._vectorAdd(
        this._vectorAdd(
          this._matrixVectorProduct(
            this._transpose(this.weights.Wz),
            dUpdateGatePre,
          ),
          this._matrixVectorProduct(
            this._transpose(this.weights.Wr),
            dResetGatePre,
          ),
        ),
        this._matrixVectorProduct(
          this._transpose(this.weights.Wh),
          dCandidateHPre,
        ),
      );

      // Gradient w.r.t. previous hidden state (more complex due to reset gate)
      const dPrevHFromUpdate = this._vectorMultiply(dh, updateGate);

      const dPrevHFromReset = this._vectorMultiply(dResetHidden, resetGate);

      const dPrevHFromUpdateGate = this._matrixVectorProduct(
        this._transpose(this.weights.Uz),
        dUpdateGatePre,
      );

      const dPrevHFromResetGate = this._matrixVectorProduct(
        this._transpose(this.weights.Ur),
        dResetGatePre,
      );

      const dPrevH = this._vectorAdd(
        this._vectorAdd(dPrevHFromUpdate, dPrevHFromReset),
        this._vectorAdd(dPrevHFromUpdateGate, dPrevHFromResetGate),
      );

      // Collect weight and bias gradients
      const dWeights = {
        Wz: dWz,
        Wr: dWr,
        Wh: dWh,
        Uz: dUz,
        Ur: dUr,
        Uh: dUh,
      };

      const dBiases = {
        bz: dBz,
        br: dBr,
        bh: dBh,
      };

      return {
        dX,
        dPrevH,
        dWeights,
        dBiases,
      };
    }

    /**
     * Backward pass for Simple RNN cell
     * @private
     * @param {Array<number>} dh - Gradient of loss w.r.t. hidden state
     * @param {Array<number>} x - Input at this time step
     * @param {Object} states - States from forward pass
     * @returns {Object} Gradients for input, previous states, and parameters
     */
    _backwardSimpleRNN(dh, x, states) {
      const { prevH, h } = states;

      // Gradient w.r.t. pre-activation
      const dPreActivation = this._vectorMultiply(dh, this._tanhDerivative(h));

      // Gradients for weights and biases
      const dWx = this._outerProduct(dPreActivation, x);
      const dWh = this._outerProduct(dPreActivation, prevH);
      const dB = dPreActivation;

      // Gradient w.r.t. input
      const dX = this._matrixVectorProduct(
        this._transpose(this.weights.Wx),
        dPreActivation,
      );

      // Gradient w.r.t. previous hidden state
      const dPrevH = this._matrixVectorProduct(
        this._transpose(this.weights.Wh),
        dPreActivation,
      );

      // Collect weight and bias gradients
      const dWeights = {
        Wx: dWx,
        Wh: dWh,
      };

      const dBiases = {
        b: dB,
      };

      return {
        dX,
        dPrevH,
        dWeights,
        dBiases,
      };
    }

    /**
     * Matrix transpose
     * @private
     * @param {Array<Array<number>>} matrix - Input matrix
     * @returns {Array<Array<number>>} Transposed matrix
     */
    _transpose(matrix) {
      const rows = matrix.length;
      const cols = matrix[0].length;

      const result = new Array(cols);
      for (let i = 0; i < cols; i++) {
        result[i] = new Array(rows);
        for (let j = 0; j < rows; j++) {
          result[i][j] = matrix[j][i];
        }
      }

      return result;
    }

    /**
     * Outer product of two vectors
     * @private
     * @param {Array<number>} a - First vector
     * @param {Array<number>} b - Second vector
     * @returns {Array<Array<number>>} Result matrix
     */
    _outerProduct(a, b) {
      const rows = a.length;
      const cols = b.length;

      const result = new Array(rows);
      for (let i = 0; i < rows; i++) {
        result[i] = new Array(cols);
        for (let j = 0; j < cols; j++) {
          result[i][j] = a[i] * b[j];
        }
      }

      return result;
    }

    /**
     * Backward pass through the recurrent layer
     * @param {Array<Array<number>>} dY - Gradient of loss with respect to output
     * @param {Object} cache - Cache from forward pass
     * @returns {Object} Gradients for weights, biases, and inputs
     */
    backward(dY, cache) {
      const startTime = performance.now();

      // Extract cache
      const { sequence, hiddenStates, cellStates, gateStates } = cache;

      // Validate gradient shape
      if (this.returnSequences) {
        if (!Array.isArray(dY) || !Array.isArray(dY[0])) {
          throw new Prime.ValidationError(
            'Output gradient must be a sequence of vectors',
          );
        }
      } else {
        if (!Array.isArray(dY)) {
          throw new Prime.ValidationError('Output gradient must be a vector');
        }
      }

      // Initialize gradients
      const dWeights = this._initializeZeroWeights();
      const dBiases = this._initializeZeroBiases();

      // Initialize input gradients
      const dX = new Array(sequence.length);
      for (let t = 0; t < sequence.length; t++) {
        dX[t] = new Array(this.inputSize).fill(0);
      }

      // Handle different gradient formats
      let dHiddenStates;
      if (this.returnSequences) {
        // Gradient for each time step
        dHiddenStates = new Array(sequence.length + 1);
        dHiddenStates.fill(0);

        // Copy gradients to hidden states (skip initial state)
        for (let t = 0; t < sequence.length; t++) {
          dHiddenStates[t + 1] = dY[t];
        }
      } else {
        // Gradient only for final time step
        dHiddenStates = new Array(sequence.length + 1);
        for (let t = 0; t < sequence.length; t++) {
          dHiddenStates[t] = new Array(this.hiddenSize).fill(0);
        }
        dHiddenStates[sequence.length] = dY;
      }

      // Initialize cell state gradients for LSTM
      let dCellStates = null;
      if (this.cellType === 'lstm') {
        dCellStates = new Array(sequence.length + 1);
        for (let t = 0; t <= sequence.length; t++) {
          dCellStates[t] = new Array(this.hiddenSize).fill(0);
        }
      }

      // Backpropagate through time (BPTT)
      for (let t = sequence.length - 1; t >= 0; t--) {
        const x = sequence[t];
        const prevH = hiddenStates[t];
        let result;

        if (this.cellType === 'lstm') {
          const prevC = cellStates[t];
          const h = hiddenStates[t + 1];
          const c = cellStates[t + 1];

          result = this._backwardLSTM(
            dHiddenStates[t + 1], // Current hidden state gradient
            dCellStates[t + 1], // Current cell state gradient
            x,
            {
              prevH,
              prevC,
              h,
              c,
              gates: gateStates[t],
            },
          );

          // Accumulate cell state gradient for previous time step
          dCellStates[t] = result.dPrevC;
        } else if (this.cellType === 'gru') {
          const h = hiddenStates[t + 1];

          result = this._backwardGRU(
            dHiddenStates[t + 1], // Current hidden state gradient
            x,
            {
              prevH,
              h,
              gates: gateStates[t],
            },
          );
        } else {
          const h = hiddenStates[t + 1];

          result = this._backwardSimpleRNN(
            dHiddenStates[t + 1], // Current hidden state gradient
            x,
            {
              prevH,
              h,
            },
          );
        }

        // Set input gradient for this time step
        dX[t] = result.dX;

        // Accumulate hidden state gradient for previous time step
        if (t > 0) {
          dHiddenStates[t] = this._vectorAdd(dHiddenStates[t], result.dPrevH);
        }

        // Accumulate weight and bias gradients
        this._accumulateGradients(dWeights, result.dWeights);
        this._accumulateGradients(dBiases, result.dBiases);
      }

      // Calculate gradient norm for monitoring
      const gradientNorm = this._calculateGradientNorm(dWeights);
      this.metrics.gradientNorm = gradientNorm;

      // Check for exploding gradients and apply gradient clipping if needed
      const clippedGradients = this._clipGradientsIfNeeded({
        dWeights,
        dBiases,
        dX,
      });

      // Update performance metrics
      const endTime = performance.now();
      this._updateBackwardMetrics(endTime - startTime);

      return clippedGradients;
    }

    /**
     * Initialize zero-filled weight gradients
     * @private
     * @returns {Object} Zero-initialized weight gradients
     */
    _initializeZeroWeights() {
      const dWeights = {};

      // Copy structure from weights but fill with zeros
      for (const key in this.weights) {
        if (Array.isArray(this.weights[key])) {
          const rows = this.weights[key].length;
          const cols = this.weights[key][0].length;

          dWeights[key] = new Array(rows);
          for (let i = 0; i < rows; i++) {
            dWeights[key][i] = new Array(cols).fill(0);
          }
        }
      }

      return dWeights;
    }

    /**
     * Initialize zero-filled bias gradients
     * @private
     * @returns {Object} Zero-initialized bias gradients
     */
    _initializeZeroBiases() {
      const dBiases = {};

      // Copy structure from biases but fill with zeros
      for (const key in this.biases) {
        if (Array.isArray(this.biases[key])) {
          dBiases[key] = new Array(this.biases[key].length).fill(0);
        }
      }

      return dBiases;
    }

    /**
     * Accumulate gradients from one time step
     * @private
     * @param {Object} accumulator - Accumulated gradients
     * @param {Object} gradients - New gradients to add
     */
    _accumulateGradients(accumulator, gradients) {
      for (const key in gradients) {
        if (Array.isArray(gradients[key])) {
          if (Array.isArray(gradients[key][0])) {
            // Handle matrices
            for (let i = 0; i < gradients[key].length; i++) {
              for (let j = 0; j < gradients[key][i].length; j++) {
                accumulator[key][i][j] += gradients[key][i][j];
              }
            }
          } else {
            // Handle vectors
            for (let i = 0; i < gradients[key].length; i++) {
              accumulator[key][i] += gradients[key][i];
            }
          }
        }
      }
    }

    /**
     * Calculate the Frobenius norm of the gradient
     * @private
     * @param {Object} dWeights - Weight gradients
     * @returns {number} Gradient norm
     */
    _calculateGradientNorm(dWeights) {
      let sumSquared = 0;

      for (const key in dWeights) {
        const matrix = dWeights[key];

        for (let i = 0; i < matrix.length; i++) {
          for (let j = 0; j < matrix[i].length; j++) {
            sumSquared += matrix[i][j] * matrix[i][j];
          }
        }
      }

      return Math.sqrt(sumSquared);
    }

    /**
     * Clip gradients if they exceed threshold to prevent explosion
     * @private
     * @param {Object} gradients - All gradients
     * @returns {Object} Clipped gradients
     */
    _clipGradientsIfNeeded(gradients) {
      const { dWeights, dBiases, dX } = gradients;

      // Gradient clipping threshold
      const maxNorm = 5.0; // Hyperparameter

      // Check if norm exceeds threshold
      if (this.metrics.gradientNorm > maxNorm) {
        // Scale factor for clipping
        const scale = maxNorm / this.metrics.gradientNorm;

        // Scale weights
        for (const key in dWeights) {
          const matrix = dWeights[key];

          for (let i = 0; i < matrix.length; i++) {
            for (let j = 0; j < matrix[i].length; j++) {
              matrix[i][j] *= scale;
            }
          }
        }

        // Scale biases
        for (const key in dBiases) {
          const vector = dBiases[key];

          for (let i = 0; i < vector.length; i++) {
            vector[i] *= scale;
          }
        }

        // Scale input gradients
        for (let t = 0; t < dX.length; t++) {
          for (let i = 0; i < dX[t].length; i++) {
            dX[t][i] *= scale;
          }
        }

        // Record coherence violation
        this._recordCoherenceViolation({
          type: 'gradient_explosion',
          severity: 'medium',
          details: {
            originalNorm: this.metrics.gradientNorm,
            clippedNorm: maxNorm,
            scale,
          },
        });

        // Update norm after clipping
        this.metrics.gradientNorm = maxNorm;
      }

      // Check for highest gradient norm
      if (
        this.metrics.gradientNorm > this.validationResults.highestGradientNorm
      ) {
        this.validationResults.highestGradientNorm = this.metrics.gradientNorm;
      }

      return { dWeights, dBiases, dX };
    }

    /**
     * Update forward performance metrics
     * @private
     * @param {number} time - Time in ms for this forward pass
     */
    _updateForwardMetrics(time) {
      this.metrics.forwardCount++;
      // Exponential moving average of forward time
      this.metrics.averageForwardTime =
        0.9 * this.metrics.averageForwardTime + 0.1 * time;
    }

    /**
     * Update backward performance metrics
     * @private
     * @param {number} time - Time in ms for this backward pass
     */
    _updateBackwardMetrics(time) {
      this.metrics.backwardCount++;
      // Exponential moving average of backward time
      this.metrics.averageBackwardTime =
        0.9 * this.metrics.averageBackwardTime + 0.1 * time;
    }

    /**
     * Update hidden state distribution statistics for coherence monitoring
     * @private
     * @param {Array<Array<number>>} hiddenStates - Hidden states over sequence
     */
    _updateHiddenStateDistribution(hiddenStates) {
      this.usagePatterns.sampleCount++;

      // Average hidden state for final state
      const finalState = hiddenStates[hiddenStates.length - 1];

      // Update hidden state distribution
      for (let i = 0; i < this.hiddenSize; i++) {
        this.usagePatterns.hiddenStateDistribution[i] =
          0.99 * this.usagePatterns.hiddenStateDistribution[i] +
          0.01 * Math.abs(finalState[i]);
      }
    }

    /**
     * Update gate activation statistics for coherence monitoring
     * @private
     * @param {Object} gates - Gate activations
     */
    _updateGateActivationStatistics(gates) {
      for (const gateType in gates) {
        if (
          gates[gateType] &&
          this.usagePatterns.gateActivationStatistics[gateType]
        ) {
          const stats = this.usagePatterns.gateActivationStatistics[gateType];

          // Update statistics for each gate unit
          for (let i = 0; i < gates[gateType].length; i++) {
            if (i < stats.length) {
              stats[i] = 0.99 * stats[i] + 0.01 * gates[gateType][i];
            }
          }
        }
      }
    }

    /**
     * Update temporal dependency statistics
     * @private
     * @param {Array<Array<number>>} hiddenStates - Hidden states over sequence
     */
    _updateTemporalDependencies(hiddenStates) {
      // Only update occasionally to avoid computation overhead
      if (this.metrics.forwardCount % 10 !== 0) return;

      // Skip if sequence is too short
      if (hiddenStates.length < 3) return;

      // Calculate correlations between states at different time steps
      const correlations = [];
      const final = hiddenStates[hiddenStates.length - 1];

      for (let t = 0; t < hiddenStates.length - 1; t++) {
        const state = hiddenStates[t];
        const correlation = this._calculateCorrelation(state, final);
        correlations.push(correlation);
      }

      // Store correlations (temporal dependencies)
      this.usagePatterns.temporalDependencies = correlations;

      // Calculate temporal coherence from correlations
      // Higher coherence = better utilization of sequence information
      let totalCorrelation = 0;
      for (let i = 0; i < correlations.length; i++) {
        // Weight more recent states higher
        const weight = i / correlations.length;
        totalCorrelation += weight * Math.abs(correlations[i]);
      }

      const temporalCoherence = totalCorrelation / correlations.length;
      this.metrics.temporalCoherence =
        0.9 * this.metrics.temporalCoherence + 0.1 * temporalCoherence;
    }

    /**
     * Calculate correlation between two vectors
     * @private
     * @param {Array<number>} a - First vector
     * @param {Array<number>} b - Second vector
     * @returns {number} Correlation coefficient
     */
    _calculateCorrelation(a, b) {
      // Center vectors
      const meanA = a.reduce((sum, val) => sum + val, 0) / a.length;
      const meanB = b.reduce((sum, val) => sum + val, 0) / b.length;

      const centeredA = a.map((val) => val - meanA);
      const centeredB = b.map((val) => val - meanB);

      // Calculate numerator (covariance)
      let numerator = 0;
      for (let i = 0; i < a.length; i++) {
        numerator += centeredA[i] * centeredB[i];
      }

      // Calculate denominators (standard deviations)
      let sumSqA = 0;
      let sumSqB = 0;

      for (let i = 0; i < a.length; i++) {
        sumSqA += centeredA[i] * centeredA[i];
        sumSqB += centeredB[i] * centeredB[i];
      }

      const denominator = Math.sqrt(sumSqA * sumSqB);

      // Avoid division by zero
      if (denominator < 1e-10) return 0;

      return numerator / denominator;
    }

    /**
     * Record coherence violation for monitoring
     * @private
     * @param {Object} violation - Violation details
     */
    _recordCoherenceViolation(violation) {
      // Add timestamp
      violation.timestamp = new Date().toISOString();

      // Add to history
      this.validationResults.violationHistory.push(violation);

      // Keep history manageable
      if (this.validationResults.violationHistory.length > 100) {
        this.validationResults.violationHistory.shift();
      }
    }

    /**
     * Monitor cell state coherence to detect exploding or vanishing gradient issues
     * @private
     * @param {Array<number>} prevCellState - Previous cell state
     * @param {Array<number>} currentCellState - Current cell state
     * @param {Array<number>} inputGate - Input gate activations
     * @param {Array<number>} forgetGate - Forget gate activations
     */
    _monitorCellStateCoherence(
      prevCellState,
      currentCellState,
      inputGate,
      forgetGate,
    ) {
      // Skip coherence check for first few iterations while cell state initializes
      if (this.metrics.forwardCount < 5) return;

      // 1. Check for exploding cell state values
      const maxCellValue = Math.max(...currentCellState.map(Math.abs));
      const explodingThreshold = 20.0; // Hyperparameter to detect explosion

      if (maxCellValue > explodingThreshold) {
        this._recordCoherenceViolation({
          type: 'cell_state_explosion',
          severity: 'high',
          details: {
            maxValue: maxCellValue,
            threshold: explodingThreshold,
          },
        });
      }

      // 2. Check for vanishing cell state
      const avgAbsCellValue =
        currentCellState.reduce((sum, val) => sum + Math.abs(val), 0) /
        currentCellState.length;
      const vanishingThreshold = 0.001; // Hyperparameter to detect vanishing

      if (avgAbsCellValue < vanishingThreshold) {
        this._recordCoherenceViolation({
          type: 'cell_state_vanishing',
          severity: 'medium',
          details: {
            avgValue: avgAbsCellValue,
            threshold: vanishingThreshold,
          },
        });
      }

      // 3. Calculate cell state change rate to detect unusual dynamics
      if (prevCellState && currentCellState) {
        let totalChange = 0;
        for (let i = 0; i < currentCellState.length; i++) {
          totalChange += Math.abs(currentCellState[i] - prevCellState[i]);
        }
        const avgChange = totalChange / currentCellState.length;

        // Unusually large changes might indicate instability
        const instabilityThreshold = 5.0; // Hyperparameter
        if (avgChange > instabilityThreshold) {
          this._recordCoherenceViolation({
            type: 'cell_state_instability',
            severity: 'medium',
            details: {
              avgChange,
              threshold: instabilityThreshold,
            },
          });
        }

        // Unusually small changes might indicate sequence forgetting
        const forgettingThreshold = 0.01; // Hyperparameter
        if (avgChange < forgettingThreshold && this.metrics.forwardCount > 20) {
          this._recordCoherenceViolation({
            type: 'cell_state_forgetting',
            severity: 'low',
            details: {
              avgChange,
              threshold: forgettingThreshold,
            },
          });
        }
      }

      // 4. Check for extreme gate activations leading to coherence issues
      // If forget gate is consistently low, information won't propagate through time
      const avgForgetGate =
        forgetGate.reduce((sum, val) => sum + val, 0) / forgetGate.length;
      if (avgForgetGate < 0.1) {
        this._recordCoherenceViolation({
          type: 'forget_gate_vanishing',
          severity: 'medium',
          details: {
            avgForgetGate,
            threshold: 0.1,
          },
        });
      }

      // If input gate is consistently high with large cell candidates, could explode
      const avgInputGate =
        inputGate.reduce((sum, val) => sum + val, 0) / inputGate.length;
      if (avgInputGate > 0.9 && maxCellValue > 10.0) {
        this._recordCoherenceViolation({
          type: 'input_gate_explosion_risk',
          severity: 'medium',
          details: {
            avgInputGate,
            maxCellValue,
            threshold: { inputGate: 0.9, cellValue: 10.0 },
          },
        });
      }
    }

    /**
     * Calculate coherence score of the layer
     * @private
     * @returns {number} Coherence score between 0 and 1
     */
    _calculateCoherenceScore() {
      // Component 1: Hidden State Distribution (0-1)
      // Higher is better - we want balanced neuron activations
      const hiddenStateDistribution =
        this.usagePatterns.hiddenStateDistribution;
      const meanActivation =
        hiddenStateDistribution.reduce((a, b) => a + b, 0) / this.hiddenSize;

      if (meanActivation === 0) return 1.0; // Not enough data yet

      const activationVariance =
        hiddenStateDistribution.reduce(
          (sum, act) => sum + Math.pow(act - meanActivation, 2),
          0,
        ) / this.hiddenSize;

      const maxVariance = Math.pow(meanActivation, 2); // Theoretical max variance
      const activationBalance = Math.max(
        0,
        1 - Math.sqrt(activationVariance / (maxVariance + 1e-10)),
      );

      // Component 2: Gate Statistics (0-1)
      // Different gates should have balanced activity
      let gateBalanceScore = 1.0;

      // For each gate type, check if it's being used appropriately
      if (this.cellType === 'lstm') {
        // Check for vanishing gradients (forget gate consistently near 0)
        const forgetGateStats =
          this.usagePatterns.gateActivationStatistics.forget;
        const avgForgetGate =
          forgetGateStats.reduce((a, b) => a + b, 0) / forgetGateStats.length;

        // Forget gate should not be consistently too low or too high
        const forgetGateBalance = 1 - Math.abs(avgForgetGate - 0.5) * 2;

        // Check for unused cells (input gate consistently near 0)
        const inputGateStats =
          this.usagePatterns.gateActivationStatistics.input;
        const avgInputGate =
          inputGateStats.reduce((a, b) => a + b, 0) / inputGateStats.length;

        // Input gate should be active enough but not always active
        const inputGateBalance = 1 - Math.abs(avgInputGate - 0.5) * 2;

        gateBalanceScore = (forgetGateBalance + inputGateBalance) / 2;
      } else if (this.cellType === 'gru') {
        // Check for reset gate balance
        const resetGateStats =
          this.usagePatterns.gateActivationStatistics.reset;
        const avgResetGate =
          resetGateStats.reduce((a, b) => a + b, 0) / resetGateStats.length;

        // Reset gate should be active sometimes but not always
        const resetGateBalance = 1 - Math.abs(avgResetGate - 0.5) * 2;

        // Check for update gate balance
        const updateGateStats =
          this.usagePatterns.gateActivationStatistics.update;
        const avgUpdateGate =
          updateGateStats.reduce((a, b) => a + b, 0) / updateGateStats.length;

        // Update gate should be balanced between new and old info
        const updateGateBalance = 1 - Math.abs(avgUpdateGate - 0.5) * 2;

        gateBalanceScore = (resetGateBalance + updateGateBalance) / 2;
      }

      // Component 3: Temporal Coherence (0-1)
      // Proper utilization of sequence information
      const temporalCoherence = this.metrics.temporalCoherence;

      // Component 4: Gradient Health (0-1)
      // Lower gradient norm is better (up to a point)
      const idealGradientNorm = 1.0; // Hyperparameter
      const maxGradientNorm = 10.0; // Hyperparameter

      const gradientHealth = Math.max(
        0,
        1 -
          Math.abs(this.metrics.gradientNorm - idealGradientNorm) /
            maxGradientNorm,
      );

      // Combine components with appropriate weights
      const coherenceScore =
        0.3 * activationBalance +
        0.3 * gateBalanceScore +
        0.2 * temporalCoherence +
        0.2 * gradientHealth;

      return coherenceScore;
    }

    /**
     * Update layer parameters with given gradients
     * @param {Object} gradients - Weight and bias gradients
     * @param {number} learningRate - Learning rate for update
     */
    update(gradients, learningRate) {
      const { dWeights, dBiases } = gradients;

      // Calculate current coherence score for monitoring
      const coherenceBefore = this._calculateCoherenceScore();
      this.validationResults.lastCoherenceScore = coherenceBefore;

      // Update weights
      for (const key in dWeights) {
        if (this.weights[key] && dWeights[key]) {
          for (let i = 0; i < this.weights[key].length; i++) {
            for (let j = 0; j < this.weights[key][i].length; j++) {
              this.weights[key][i][j] -= learningRate * dWeights[key][i][j];
            }
          }
        }
      }

      // Update biases
      for (const key in dBiases) {
        if (this.biases[key] && dBiases[key]) {
          for (let i = 0; i < this.biases[key].length; i++) {
            this.biases[key][i] -= learningRate * dBiases[key][i];
          }
        }
      }

      // Validate parameters after update
      this._validateParameters();

      // Update coherence metric
      const coherenceAfter = this._calculateCoherenceScore();
      this.metrics.coherence = coherenceAfter;

      // Detect significant coherence drops
      if (coherenceAfter < coherenceBefore * 0.8) {
        this._recordCoherenceViolation({
          type: 'coherence_drop',
          severity: 'medium',
          details: {
            before: coherenceBefore,
            after: coherenceAfter,
            drop: coherenceBefore - coherenceAfter,
          },
        });
      }
    }

    /**
     * Validate parameters for numerical issues
     * @private
     */
    _validateParameters() {
      // Check for NaN/Infinity in weights and biases
      for (const key in this.weights) {
        const matrix = this.weights[key];

        for (let i = 0; i < matrix.length; i++) {
          for (let j = 0; j < matrix[i].length; j++) {
            if (!Number.isFinite(matrix[i][j])) {
              // Replace with zero and record violation
              matrix[i][j] = 0;

              this._recordCoherenceViolation({
                type: 'non_finite_weight',
                severity: 'high',
                details: {
                  parameter: `weights.${key}[${i}][${j}]`,
                },
              });
            }
          }
        }
      }

      for (const key in this.biases) {
        const vector = this.biases[key];

        for (let i = 0; i < vector.length; i++) {
          if (!Number.isFinite(vector[i])) {
            // Replace with zero and record violation
            vector[i] = 0;

            this._recordCoherenceViolation({
              type: 'non_finite_bias',
              severity: 'high',
              details: {
                parameter: `biases.${key}[${i}]`,
              },
            });
          }
        }
      }
    }

    /**
     * Get layer performance metrics
     * @returns {Object} Current performance metrics
     */
    getMetrics() {
      // Ensure coherence is up to date
      this.metrics.coherence = this._calculateCoherenceScore();
      return { ...this.metrics };
    }

    /**
     * Get layer usage patterns
     * @returns {Object} Current usage patterns
     */
    getUsagePatterns() {
      return {
        hiddenStateDistribution: [
          ...this.usagePatterns.hiddenStateDistribution,
        ],
        gateActivationStatistics: JSON.parse(
          JSON.stringify(this.usagePatterns.gateActivationStatistics),
        ),
        temporalDependencies: [...this.usagePatterns.temporalDependencies],
        sampleCount: this.usagePatterns.sampleCount,
      };
    }

    /**
     * Get coherence validation history
     * @returns {Object} Validation results and history
     */
    getValidationHistory() {
      return {
        coherenceScore: this.metrics.coherence,
        violationHistory: [...this.validationResults.violationHistory],
        highestGradientNorm: this.validationResults.highestGradientNorm,
      };
    }

    /**
     * Get information about the layer architecture
     * @returns {Object} Layer architecture information
     */
    getArchitecture() {
      return {
        type: 'recurrent',
        cellType: this.cellType,
        inputSize: this.inputSize,
        hiddenSize: this.hiddenSize,
        sequenceLength: this.sequenceLength,
        returnSequences: this.returnSequences,
        parameterCount: this._countParameters(),
      };
    }

    /**
     * Count total number of parameters in the layer
     * @private
     * @returns {number} Parameter count
     */
    _countParameters() {
      let count = 0;

      // Count weights
      for (const key in this.weights) {
        const matrix = this.weights[key];
        count += matrix.length * matrix[0].length;
      }

      // Count biases
      for (const key in this.biases) {
        count += this.biases[key].length;
      }

      return count;
    }
  }

  // Add class to Prime.Neural namespace
  Prime.Neural = Prime.Neural || {};
  Prime.Neural.Layer = Prime.Neural.Layer || {};
  Prime.Neural.Layer.RecurrentLayer = RecurrentLayer;
})();

// Export the enhanced Prime object
module.exports = Prime;
