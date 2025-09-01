#include "utils/graphs/Graph2DBiConcurrent.hpp"

namespace gracfl {
    Graph2DBiConcurrent::Graph2DBiConcurrent(std::string& graphfilepath, const Grammar& grammar)
        : Graph(graphfilepath, grammar) 
    {
        initContainers();
        addInitialEdges();
    }

    Graph2DBiConcurrent::Graph2DBiConcurrent(std::vector<Edge>& edges, const Grammar& grammar)
        : Graph(edges, grammar) 
    {
        initContainers();
        addInitialEdges();
    }

    void Graph2DBiConcurrent::initContainers()
    {
        outEdges_.assign(getNodeSize(), TemporalVectorConcurrentWithLbldVtx());
        inEdges_.assign(getNodeSize(), TemporalVectorConcurrentWithLbldVtx());
        hashset_.assign(getNodeSize(), std::vector<tbb::concurrent_unordered_set<ull>>(getLabelSize(), tbb::concurrent_unordered_set<ull>()));
    }

    void Graph2DBiConcurrent::addInitialEdges()
    {
        for (Edge edge : getEdges())
        {
            hashset_[edge.from][edge.label].insert(edge.to);
            outEdges_[edge.from].vertexList.push_back(LbldVtx(edge.to, edge.label));
            inEdges_[edge.to].vertexList.push_back(LbldVtx(edge.from, edge.label));

            // update the sliding pointers
            outEdges_[edge.from].NEW_END++;
            inEdges_[edge.to].NEW_END++;
        }
    }

    void Graph2DBiConcurrent::clearContainers()
    {
        outEdges_.clear();
        inEdges_.clear();
        hashset_.clear();
    }


    void Graph2DBiConcurrent::checkAndAddEdge(Edge& edge, bool& terminate)
    {
        if (hashset_[edge.from][edge.label].find(edge.to) == hashset_[edge.from][edge.label].end()) {
            hashset_[edge.from][edge.label].insert(edge.to);
            outEdges_[edge.from].vertexList.push_back(LbldVtx(edge.to, edge.label));
            inEdges_[edge.to].vertexList.push_back(LbldVtx(edge.from, edge.label));
            terminate = false;
        }
    }

    void Graph2DBiConcurrent::addSelfEdge(Edge& edge)
    {
        if (hashset_[edge.from][edge.label].find(edge.to) == hashset_[edge.from][edge.label].end())
        {
            hashset_[edge.from][edge.label].insert(edge.to);
            outEdges_[edge.from].vertexList.push_back(LbldVtx(edge.to, edge.label));
            outEdges_[edge.from].NEW_END++;
            inEdges_[edge.to].vertexList.push_back(LbldVtx(edge.from, edge.label));
            inEdges_[edge.to].NEW_END++;
        }
    }

    ull Graph2DBiConcurrent::countEdge()
    {
        return countEdgeHelperConcurrent(hashset_);;
    }
}