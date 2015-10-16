#include <iostream>
#include <vector>
#include <queue>
#include <cassert>

using namespace std;

class Graph{
public:
	class Edge{
	public:
		size_t from, to;
		long long capacity;
		Edge(size_t from, size_t to, long long capacity) : from(from), to(to), capacity(capacity) {}
	};
	vector<Edge> edge;
	size_t vertices;

	Graph() : vertices(0)
	{
	}

	void addEdge(size_t from, size_t to, long long capacity){
		edge.push_back(Edge(from, to, capacity));
		vertices = max(vertices, max(from + 1, to + 1));
	}

	void read(){
		size_t edges;
		cin >> vertices >> edges;
		for (size_t edge = 0; edge < edges; ++edge){
			size_t from, to, capacity;
			cin >> from >> to >> capacity;
			addEdge(from - 1, to - 1, capacity);
		}
	}
};

class Network{
public:
	struct Link{
		long long flow, capacity;
		Link() : flow(0), capacity(0)
		{
		}
		bool isSaturated() const{
			return flow == capacity;
		}

		long long getRemainingCapacity(){
			return capacity - flow;
		}
	};

	vector<vector<Link> > link;
	size_t nodes, source, sink;
	long long totalFlow;
	void addEdge(Graph::Edge edge){
		link[edge.from][edge.to].capacity += edge.capacity;
	}

	Network(const Graph &graph) : link(graph.vertices, std::vector<Link>(graph.vertices)),
		nodes(graph.vertices), source(0), sink(graph.vertices - 1), totalFlow(0){
		for (size_t edgeId = 0; edgeId < graph.edge.size(); ++edgeId)
			addEdge(graph.edge[edgeId]);
	}

	void push(size_t from, size_t to, long long delta){
		link[from][to].flow += delta;
		link[to][from].flow -= delta;
		assert(link[from][to].flow <= link[from][to].capacity);
	}

};

class MaxFlowAlgorithm{
public:
	Network *network;
	long long totalFlow;

	MaxFlowAlgorithm(Network *network) : network(network), totalFlow(0)
	{
	}

	virtual void run() = 0;
};

class MKMAlgorithm : public MaxFlowAlgorithm{
public:
	class BFS{
	public:
		Network *network;
		vector<size_t> level;
		vector<bool> visited;

		void reset(){
			fill(visited.begin(), visited.end(), false);
		}

		void run(){
			reset();
			std::queue<size_t> queue;
			queue.push(network->source);
			level[network->source] = 0;
			visited[network->source] = true;
			while (!queue.empty()){
				size_t node = queue.front();
				queue.pop();
				for (size_t to = 0; to < network->nodes; ++to){
					if (visited[to])
						continue;
					const Network::Link &link = network->link[node][to];
					if (link.isSaturated())
						continue;
					level[to] = level[node] + 1;
					visited[to] = true;
					queue.push(to);
				}
			}
		}

		BFS(Network *network) : network(network), level(network->nodes), visited(network->nodes)
		{
		}

		bool isPathFound() const{
			return visited[network->sink];
		}

		bool betweenLevels(size_t from, size_t to) const{
			return level[from] + 1 == level[to];
		}

		bool usefulNode(size_t node) const{
			if (!visited[node])
				return false;
			return node == network->sink || level[node] < level[network->sink];
		}
	};
	BFS bfs;
	vector<long long> outCapacity, inCapacity;
	vector<bool> usedNode;
	vector<size_t> pointer[2];

	MKMAlgorithm(Network *network) : MaxFlowAlgorithm(network), bfs(network),
		outCapacity(network->nodes), inCapacity(network->nodes), usedNode(network->nodes){
		pointer[0] = pointer[1] = std::vector<size_t>(network->nodes);
	}

	long long getPotential(size_t node){
		if (node == network->source)
			return outCapacity[node];
		else if (node == network->sink)
			return inCapacity[node];
		else
			return min(inCapacity[node], outCapacity[node]);
	}

	void pushPreflow(size_t node, long long flow, bool direction){
		if (flow == 0)
			return;
		if (direction == 0 && node == network->sink)
			return;
		if (direction == 1 && node == network->source)
			return;
		for (size_t &next = pointer[direction][node]; next < network->nodes; ++next){
			size_t from = node, to = next;
			if (direction)
				std::swap(from, to);
			if (usedNode[next])
				continue;
			if (!bfs.betweenLevels(from, to))
				continue;
			if (network->link[from][to].isSaturated())
				continue;
			long long delta = min(flow, network->link[from][to].getRemainingCapacity());

			outCapacity[from] -= delta;
			inCapacity[to] -= delta;
			network->push(from, to, delta);
			flow -= delta;
			pushPreflow(next, delta, direction);
			if (flow == 0)
				break;
		}
		assert(flow == 0);
	}

	void initBlockingFlow(){
		fill(pointer[0].begin(), pointer[0].end(), 0);
		fill(pointer[1].begin(), pointer[1].end(), 0);
		fill(outCapacity.begin(), outCapacity.end(), 0);
		fill(inCapacity.begin(), inCapacity.end(), 0);

		for (size_t node = 0; node < network->nodes; ++node)
			usedNode[node] = !bfs.usefulNode(node);
		for (size_t node = 0; node < network->nodes; ++node)
		{
			if (usedNode[node])
				continue;
			for (size_t to = 0; to < network->nodes; ++to)
			if (bfs.betweenLevels(node, to) && !usedNode[to])
			{
				long long capacity = network->link[node][to].getRemainingCapacity();
				outCapacity[node] += capacity;
				inCapacity[to] += capacity;
			}
		}
	}

	void deleteNode(size_t node){
		usedNode[node] = true;
		for (size_t to = 0; to < network->nodes; ++to){
			if (usedNode[to])
				continue;
			if (bfs.betweenLevels(node, to))
				inCapacity[to] -= network->link[node][to].getRemainingCapacity();
			if (bfs.betweenLevels(to, node))
				outCapacity[to] -= network->link[to][node].getRemainingCapacity();
		}
	}

	void findBlockingFlow(){
		initBlockingFlow();
		while (true){
			size_t node = network->nodes;
			for (size_t candidate = 0; candidate < network->nodes; ++candidate){
				if (usedNode[candidate])
					continue;
				if (node == network->nodes || getPotential(candidate) < getPotential(node))
					node = candidate;
			}
			if (node == network->nodes)
				break;
			long long delta = getPotential(node);
			totalFlow += delta;
			pushPreflow(node, delta, 0);
			pushPreflow(node, delta, 1);
			deleteNode(node);
		}
	}

	virtual void run(){
		while (true){
			bfs.run();
			if (!bfs.isPathFound())
				break;
			findBlockingFlow();
		}
	}
};

class PushRelabelAlgorithm : public MaxFlowAlgorithm{
public:
	vector<size_t> height;
	vector<long long> extra;
	vector<size_t> pointer;

	void push(size_t from, size_t to, long long delta){
		extra[to] += delta;
		extra[from] -= delta;
		network->push(from, to, delta);
	}

	bool canPush(size_t from, size_t to){
		return height[from] == height[to] + 1;
	}

	void initPreflow(){
		height[network->source] = network->nodes;
		for (size_t node = 0; node < network->nodes; ++node){
			long long delta = network->link[network->source][node].getRemainingCapacity();
			push(network->source, node, delta);
		}
	}

	bool overflowed(size_t node){
		return node != network->sink && node != network->source && extra[node] > 0;
	}

	PushRelabelAlgorithm(Network *network) : MaxFlowAlgorithm(network), height(network->nodes),
		extra(network->nodes), pointer(network->nodes){
	}

	void lift(size_t node){
		assert(node != network->source && extra[node] > 0);
		size_t newHeight = network->nodes * 2;
		for (size_t to = 0; to < network->nodes; ++to){
			if (network->link[node][to].isSaturated())
				continue;
			newHeight = std::min(newHeight, height[to] + 1);
		}
		height[node] = newHeight;
	}

	void discharge(size_t node){
		while (extra[node] > 0){
			size_t &to = pointer[node];
			if (to == network->nodes){
				lift(node);
				to = 0;
				continue;
			}
			if (canPush(node, to)){
				size_t delta = min(extra[node], network->link[node][to].getRemainingCapacity());
				push(node, to, delta);
			}
			++to;
		}
	}

	virtual void run(){
		initPreflow();
		bool changed = true;
		while (changed){
			changed = false;
			for (size_t node = 0; node < network->nodes; ++node){
				if (overflowed(node)){
					changed = true;
					discharge(node);
				}
			}
		}
		for (size_t node = 0; node < network->nodes; ++node)
		if (node != network->source)
			totalFlow += network->link[network->source][node].flow;
	}
};

int main(){
	Graph graph;
	graph.read();
	Network network(graph);
	MaxFlowAlgorithm *FlowWorker = new PushRelabelAlgorithm(&network);
	FlowWorker->run();
	std::cout << FlowWorker->totalFlow << '\n';
	for (size_t edgeId = 0; edgeId < graph.edge.size(); ++edgeId)
	{
		Graph::Edge edge = graph.edge[edgeId];
		long long flow = network.link [edge.from][edge.to].flow;
		long long result = std::max(long long(0), std::min(flow, edge.capacity));
		network.push(edge.to, edge.from, result);
		std::cout << result << '\n';
	}
	system("pause");
}