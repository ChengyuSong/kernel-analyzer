#include "utils/graphs/Graph3DIn.hpp"

namespace gracfl {
    Graph3DIn::Graph3DIn(std::string& graphfilepath, const Grammar& grammar)
        : Graph(graphfilepath, grammar) 
    {
        initContainers();
        addInitialEdges();
    }

    Graph3DIn::Graph3DIn(std::vector<Edge>& edges, const Grammar& grammar)
        : Graph(edges, grammar) 
    {
        initContainers();
        addInitialEdges();
    }

    void Graph3DIn::initContainers()
    {
        inEdges_.assign(getNodeSize(), std::vector<TemporalVector>(getLabelSize()));
        inHashset_.assign(getNodeSize(), std::vector<std::unordered_set<ull>>(getLabelSize(), std::unordered_set<ull>()));
    }

    void Graph3DIn::addInitialEdges()
    {
        for (Edge edge : getEdges())
        {
            inHashset_[edge.to][edge.label].insert(edge.from);
            inEdges_[edge.to][edge.label].vertexList.push_back(edge.from);

            // update the sliding pointers
            inEdges_[edge.to][edge.label].NEW_END++;
        }
    }

    void Graph3DIn::clearContainers()
    {
        inEdges_.clear();
        inHashset_.clear();
    }

    void Graph3DIn::checkAndAddEdge(Edge& edge, bool& terminate)
    {
        if (inHashset_[edge.to][edge.label].find(edge.from) == inHashset_[edge.to][edge.label].end()) {
            inHashset_[edge.to][edge.label].insert(edge.from);
            inEdges_[edge.to][edge.label].vertexList.push_back(edge.from);
            terminate = false;
        }
    }
    
    void Graph3DIn::addSelfEdge(Edge& edge)
    {
        if (inHashset_[edge.to][edge.label].find(edge.from) == inHashset_[edge.to][edge.label].end())
        {
            inHashset_[edge.to][edge.label].insert(edge.from);
            inEdges_[edge.to][edge.label].vertexList.push_back(edge.from);
            inEdges_[edge.to][edge.label].NEW_END++;
        }
    }

    ull Graph3DIn::countEdge()
    {
        return countEdgeHelper(inHashset_);
    }
}