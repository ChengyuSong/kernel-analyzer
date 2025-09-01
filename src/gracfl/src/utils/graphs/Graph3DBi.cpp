#include "utils/graphs/Graph3DBi.hpp"

namespace gracfl {
    Graph3DBi::Graph3DBi(std::string& graphfilepath, const Grammar& grammar)
        : Graph(graphfilepath, grammar) 
    {
        initContainers();
        addInitialEdges();
    }

    Graph3DBi::Graph3DBi(std::vector<Edge>& edges, const Grammar& grammar)
        : Graph(edges, grammar) 
    {
        initContainers();
        addInitialEdges();
    }

    void Graph3DBi::initContainers()
    {
        outEdges_.assign(getNodeSize(), std::vector<TemporalVector>(getLabelSize()));
        inEdges_.assign(getNodeSize(), std::vector<TemporalVector>(getLabelSize()));
        hashset_.assign(getNodeSize(), std::vector<std::unordered_set<ull>>(getLabelSize(), std::unordered_set<ull>()));
    }

    void Graph3DBi::addInitialEdges()
    {
        for (Edge edge : getEdges())
        {
            hashset_[edge.from][edge.label].insert(edge.to);
            outEdges_[edge.from][edge.label].vertexList.push_back(edge.to);
            inEdges_[edge.to][edge.label].vertexList.push_back(edge.from);

            // update the sliding pointers
            outEdges_[edge.from][edge.label].NEW_END++;
            inEdges_[edge.to][edge.label].NEW_END++;
        }
    }

    void Graph3DBi::clearContainers()
    {
        outEdges_.clear();
        inEdges_.clear();
        hashset_.clear();
    }


    void Graph3DBi::checkAndAddEdge(Edge& edge, bool& terminate)
    {
        if (hashset_[edge.from][edge.label].find(edge.to) == hashset_[edge.from][edge.label].end()) {
            hashset_[edge.from][edge.label].insert(edge.to);
            outEdges_[edge.from][edge.label].vertexList.push_back(edge.to);
            inEdges_[edge.to][edge.label].vertexList.push_back(edge.from);
            terminate = false;
        }
    }

    void Graph3DBi::addSelfEdge(Edge& edge)
    {
        if (hashset_[edge.from][edge.label].find(edge.to) == hashset_[edge.from][edge.label].end())
        {
            hashset_[edge.from][edge.label].insert(edge.to);
            outEdges_[edge.from][edge.label].vertexList.push_back(edge.to);
            outEdges_[edge.from][edge.label].NEW_END++;
            inEdges_[edge.to][edge.label].vertexList.push_back(edge.from);
            inEdges_[edge.to][edge.label].NEW_END++;
        }
    }

    ull Graph3DBi::countEdge()
    {
        return countEdgeHelper(hashset_);
    }
}