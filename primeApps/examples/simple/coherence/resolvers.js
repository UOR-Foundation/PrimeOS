/**
 * Simple Example PrimeApp Resolvers
 */

class MessageConflictResolver {
  /**
   * Resolve conflicts between messages
   * @param {Object} conflict - Conflict to resolve
   * @returns {Object} - Resolved object
   */
  async resolve(conflict) {
    const { local, remote, path } = conflict;
    
    // Default to most recent version
    return conflict.timestamps.local > conflict.timestamps.remote 
      ? local 
      : remote;
  }
}

module.exports = {
  MessageConflictResolver
};