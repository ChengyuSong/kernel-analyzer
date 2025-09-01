#include "utils/graphs/Graph3DOut.hpp"

namespace gracfl {
    Graph3DOut::Graph3DOut(std::string& graphfilepath, const Grammar& grammar)
        : Graph(graphfilepath, grammar) 
    {
        initContainers();
        addInitialEdges();
    }

    Graph3DOut::Graph3DOut(std::vector<Edge>& edges, const Grammar& grammar)
        : Graph(edges, grammar) 
    {
        initContainers();
        addInitialEdges();
    }
    
    void Graph3DOut::initContainers()
    {
        outEdges_.assign(getNodeSize(), std::vector<TemporalVector>(getLabelSize()));
        hashset_.assign(getNodeSize(), std::vector<std::unordered_set<ull>>(getLabelSize(), std::unordered_set<ull>()));
    }

    void Graph3DOut::addInitialEdges()
    {
        for (Edge edge : getEdges())
        {
            hashset_[edge.from][edge.label].insert(edge.to);
            outEdges_[edge.from][edge.label].vertexList.push_back(edge.to);

            // update the sliding pointers
            outEdges_[edge.from][edge.label].NEW_END++;
        }
    }

    void Graph3DOut::clearContainers()
    {
        outEdges_.clear();
        hashset_.clear();
    }

    void Graph3DOut::checkAndAddEdge(Edge& edge, bool& terminate)
    {
        if (hashset_[edge.from][edge.label].find(edge.to) == hashset_[edge.from][edge.label].end()) {
            hashset_[edge.from][edge.label].insert(edge.to);
            outEdges_[edge.from][edge.label].vertexList.push_back(edge.to);
            terminate = false;
        }
    }

    void Graph3DOut::addSelfEdge(Edge& edge)
    {
        if (hashset_[edge.from][edge.label].find(edge.to) == hashset_[edge.from][edge.label].end())
        {
            hashset_[edge.from][edge.label].insert(edge.to);
            outEdges_[edge.from][edge.label].vertexList.push_back(edge.to);
            outEdges_[edge.from][edge.label].NEW_END++;
        }
    }

    ull Graph3DOut::countEdge()
    {
        return countEdgeHelper(hashset_);
    }
}