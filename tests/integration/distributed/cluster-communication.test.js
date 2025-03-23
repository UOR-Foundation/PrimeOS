/**
 * Integration tests for PrimeOS Distributed Computation Module - Cluster and Communication
 */

const Prime = require("../../../src");
const { assertions, mocking } = require("../../utils");

describe("Distributed Cluster and Communication Integration", () => {
  let clusterManager;
  let communicationHub;
  
  beforeEach(() => {
    // Set up a cluster manager with communication capabilities
    clusterManager = new Prime.Distributed.Cluster.ClusterManager({
      discoveryMethod: "local",
      maxNodes: 5
    });
    
    // Create communication hub
    communicationHub = new Prime.Distributed.Communication.CommunicationHub({
      clusterManager
    });
    
    // Add worker nodes to the cluster
    clusterManager.addNode({
      id: "worker_1",
      type: Prime.Distributed.Cluster.NodeType.WORKER,
      address: "localhost",
      port: 9001
    });
    
    clusterManager.addNode({
      id: "worker_2",
      type: Prime.Distributed.Cluster.NodeType.WORKER,
      address: "localhost",
      port: 9002
    });
  });
  
  test("cluster manager integrates with communication hub", () => {
    // Verify the integration between cluster manager and communication hub
    expect(communicationHub.clusterManager).toBe(clusterManager);
    expect(communicationHub.getNodeCount()).toBe(2);
    
    // Verify communication channels are created for each node
    const channels = communicationHub.getChannels();
    expect(Object.keys(channels).length).toBe(2);
    expect(channels["worker_1"]).toBeDefined();
    expect(channels["worker_2"]).toBeDefined();
  });
  
  test("messages are routed between nodes correctly", async () => {
    // Create a test message
    const testMessage = {
      id: "msg_123",
      type: Prime.Distributed.Communication.MessageType.TASK_ASSIGNMENT,
      source: "coordinator",
      destination: "worker_1",
      payload: {
        taskId: "task_1",
        data: { x: 1, y: 2 }
      }
    };
    
    // Set up message receipt tracking
    let receivedMessage = null;
    const worker1Channel = communicationHub.getChannelForNode("worker_1");
    
    // Mock the channel's receive method
    const originalReceive = worker1Channel.receive;
    worker1Channel.receive = jest.fn().mockImplementation(message => {
      receivedMessage = message;
      return Promise.resolve({ status: "received" });
    });
    
    // Send message through the communication hub
    await communicationHub.routeMessage(testMessage);
    
    // Verify message was routed correctly
    expect(worker1Channel.receive).toHaveBeenCalled();
    expect(receivedMessage).toBeDefined();
    expect(receivedMessage.id).toBe("msg_123");
    expect(receivedMessage.destination).toBe("worker_1");
    
    // Restore original method
    worker1Channel.receive = originalReceive;
  });
  
  test("cluster status is monitored and reported correctly", async () => {
    // Setup node status reporting
    for (const nodeId of ["worker_1", "worker_2"]) {
      const node = clusterManager.getNode(nodeId);
      node.updateStatus({
        cpuUsage: 0.3,
        memoryUsage: 0.4,
        tasksProcessed: 5,
        isReady: true
      });
    }
    
    // Get cluster status through communication hub
    const status = await communicationHub.getClusterStatus();
    
    // Verify cluster status information
    expect(status).toBeDefined();
    expect(status.nodes).toBeDefined();
    expect(Object.keys(status.nodes).length).toBe(2);
    expect(status.nodes["worker_1"]).toBeDefined();
    expect(status.nodes["worker_1"].isReady).toBe(true);
    expect(status.aggregates).toBeDefined();
    expect(status.aggregates.totalNodes).toBe(2);
    expect(status.aggregates.readyNodes).toBe(2);
  });
  
  test("task messages are processed in order of priority", async () => {
    // Create task messages with different priorities
    const highPriorityTask = {
      id: "task_high",
      type: Prime.Distributed.Communication.MessageType.TASK_ASSIGNMENT,
      source: "coordinator",
      destination: "worker_1",
      priority: "high",
      payload: { taskId: "high_priority" }
    };
    
    const mediumPriorityTask = {
      id: "task_medium",
      type: Prime.Distributed.Communication.MessageType.TASK_ASSIGNMENT,
      source: "coordinator",
      destination: "worker_1",
      priority: "medium",
      payload: { taskId: "medium_priority" }
    };
    
    const lowPriorityTask = {
      id: "task_low",
      type: Prime.Distributed.Communication.MessageType.TASK_ASSIGNMENT,
      source: "coordinator",
      destination: "worker_1",
      priority: "low",
      payload: { taskId: "low_priority" }
    };
    
    // Track processed messages
    const processedTasks = [];
    
    // Mock the worker's task processor
    const worker1 = clusterManager.getNode("worker_1");
    const originalProcessTask = worker1.processTask;
    worker1.processTask = jest.fn().mockImplementation(task => {
      processedTasks.push(task.payload.taskId);
      return Promise.resolve({ status: "completed" });
    });
    
    // Send tasks in reverse priority order
    await communicationHub.routeMessage(lowPriorityTask);
    await communicationHub.routeMessage(highPriorityTask);
    await communicationHub.routeMessage(mediumPriorityTask);
    
    // Process the message queue
    await communicationHub.processMessageQueue("worker_1");
    
    // Verify tasks were processed in correct priority order
    expect(processedTasks.length).toBe(3);
    expect(processedTasks[0]).toBe("high_priority");
    expect(processedTasks[1]).toBe("medium_priority");
    expect(processedTasks[2]).toBe("low_priority");
    
    // Restore original method
    worker1.processTask = originalProcessTask;
  });
});