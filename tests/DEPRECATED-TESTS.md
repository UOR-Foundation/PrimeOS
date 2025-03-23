# Deprecated Test Files
  
This document lists all the deprecated test files from the old test structure
and their replacements in the new structure.

| Old Test File | Replacement(s) |
|---------------|---------------|
| attention-mechanism-tests.js | unit/consciousness/attention.test.js |
| coherence-tests.js | unit/coherence/verification.test.js |
| coherence-validator-refactor-test.js | unit/coherence/validator.test.js |
| coherence-verification-patched.js | unit/coherence/verification.test.js |
| coherence-verification.js | unit/coherence/verification.test.js |
| consciousness-integration-tests.js | integration/consciousness/memory-temporal.test.js |
| consciousness-module-tests.js | unit/consciousness/module.test.js |
| consciousness-tests.js | unit/consciousness/module.test.js |
| conv-memory-test.js | unit/consciousness/memory.test.js |
| core-tests.js | unit/core/ |
| distributed-coherence-benchmarks.js | performance/distributed/ |
| distributed-coherence-integration-tests.js | integration/distributed/partition-coherence.test.js |
| distributed-coherence-mock-network.js | unit/distributed/communication.test.js |
| distributed-integration-test.js | integration/distributed/cluster-communication.test.js |
| distributed-pipeline-tests.js | integration/distributed/training-pipeline.test.js |
| distributed-tests.js | unit/distributed/ |
| distributed-training-test.js | unit/distributed/training.test.js |
| extreme-conditions-basic-test.js | extreme/math/matrix-operations-extreme.test.js |
| extreme-conditions-tests.js | extreme/math/matrix-operations-extreme.test.js |
| framework-tests.js | unit/framework/ |
| integration-tests.js | integration/ |
| manifold-operations-tests.js | unit/math/lie-groups.test.js |
| mathematics-tests.js | unit/math/ |
| matrix-edge-cases-tests.js | extreme/math/matrix-extreme.test.js |
| matrix-extreme-values-svd-tests.js | extreme/math/svd-extreme.test.js |
| matrix-extreme-values-svd.js | extreme/math/svd-extreme.test.js |
| matrix-extreme-values-tests.js | extreme/math/matrix-extreme.test.js |
| matrix-refactor-tests.js | unit/math/matrix.test.js |
| matrix-stability-test.js | extreme/math/matrix-operations-extreme.test.js |
| model-management-test.js | unit/neural/model.test.js |
| neural-advanced-tests.js | unit/neural/ |
| neural-distributed-test.js | integration/distributed/training-pipeline.test.js |
| neural-model-test.js | unit/neural/model.test.js |
| neural-refactor-test.js | unit/neural/model.test.js |
| neural-tests.js | unit/neural/ |
| pattern-recognition-tests.js | unit/framework/base1.test.js |
| prime-math-tests.js | unit/math/precision.test.js |
| prime-os-verification-tests.js | unit/core/ |
| refactor-verification.js | unit/coherence/verification.test.js |
| svd-basic-test.js | unit/math/matrix.test.js |
| uor-verification-tests.js | unit/coherence/uor.test.js |
| vector-refactor-test.js | unit/math/vector.test.js |

## Migration Status

All tests from the old structure have been migrated to the new structure.
The old test files are kept temporarily for reference but will be removed
in a future update.

For details on the test refactoring, see [tests-refactor-plan.md](tests-refactor-plan.md).
