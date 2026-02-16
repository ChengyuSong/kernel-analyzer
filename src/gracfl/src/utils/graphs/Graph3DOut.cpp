#include "utils/graphs/Graph3DOut.hpp"

namespace gracfl {
    Graph3DOut::Graph3DOut(std::string& graphfilepath, const Grammar& grammar)
        : Graph(graphfilepath, grammar) 
    {
        initContainers();
        addInitialEdges();
    }

    Graph3DOut::Graph3DOut(const std::vector<Edge>& edges, const Grammar& grammar)
        : Graph(edges, grammar) 
    {
        initContainers();
        addInitialEdges();
    }
    
    void Graph3DOut::initContainers()
    {
        outEdges_.assign(getNodeSize(), std::vector<TemporalVector>(getLabelSize()));
        hashset_.assign(getNodeSize(), std::vector<ReachabilitySet>(getLabelSize(), ReachabilitySet()));
    }

    void Graph3DOut::addInitialEdges()
    {
        for (const Edge& edge : getEdges())
        {
            auto& set = hashset_[edge.from][edge.label];
            auto it = set.insert(edge.to);
            if (it.second) {
                outEdges_[edge.from][edge.label].vertexList.push_back(edge.to);

                // update the sliding pointers
                outEdges_[edge.from][edge.label].NEW_END++;
            }
        }
    }

    void Graph3DOut::clearContainers()
    {
        outEdges_.clear();
        hashset_.clear();
    }

    bool Graph3DOut::checkAndAddEdge(const Edge& edge)
    {
        auto& set = hashset_[edge.from][edge.label];
        auto it = set.insert(edge.to);
        if (it.second) {
            outEdges_[edge.from][edge.label].vertexList.push_back(edge.to);
            return true;
        }
        return false;
    }

    void Graph3DOut::addSelfEdge(Edge& edge)
    {
        auto& set = hashset_[edge.from][edge.label];
        auto it = set.insert(edge.to);
        if (it.second) {
            outEdges_[edge.from][edge.label].vertexList.push_back(edge.to);
            outEdges_[edge.from][edge.label].NEW_END++;
        }
    }

    ull Graph3DOut::countEdge()
    {
        ull size = 0;
        for (uint i = 0; i < hashset_.size(); i++)
        {
            for (uint j = 0; j < hashset_[i].size(); j++)
            {
                size += hashset_[i][j].size();
            }
        }
        return size;
    }
}
