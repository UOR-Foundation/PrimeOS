/**
 * Unit tests for PrimeOS Distributed Computation Module - Communication components
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("PrimeOS Distributed Computation Module - Communication", () => {
  describe("CommunicationChannel", () => {
    test("creates a communication channel with correct properties", () => {
      const channel = new Prime.Distributed.Communication.CommunicationChannel({
        nodeId: "test_node_3",
      });

      expect(channel instanceof Prime.Distributed.Communication.CommunicationChannel).toBe(true);
      expect(channel.nodeId).toBe("test_node_3");
      expect(channel.isConnected()).toBe(true);

      // Test channel metrics
      const metrics = channel.getMetrics();
      expect(typeof metrics).toBe("object");
      expect(metrics.messagesSent).toBe(0);
      expect(metrics.messagesReceived).toBe(0);
    });
  });

  describe("MessageRouter", () => {
    test("creates a message router with correct properties", () => {
      const router = new Prime.Distributed.Communication.MessageRouter({
        nodeId: "test_node_4",
      });

      expect(router instanceof Prime.Distributed.Communication.MessageRouter).toBe(true);
      expect(router.nodeId).toBe("test_node_4");
      expect(router.channel instanceof Prime.Distributed.Communication.CommunicationChannel).toBe(true);
    });

    test("registers and handles message handlers correctly", () => {
      const router = new Prime.Distributed.Communication.MessageRouter({
        nodeId: "test_node_4",
      });

      // Register a custom handler
      let handlerCalled = false;

      router.registerHandler(
        Prime.Distributed.Communication.MessageType.HEARTBEAT,
        (message) => {
          handlerCalled = true;
          return Promise.resolve({ handled: true });
        },
      );

      // Test router metrics
      const metrics = router.getMetrics();
      expect(typeof metrics).toBe("object");
      expect(typeof metrics.messagesRouted).toBe("number");
      expect(typeof metrics.channel).toBe("object");
    });
  });
});