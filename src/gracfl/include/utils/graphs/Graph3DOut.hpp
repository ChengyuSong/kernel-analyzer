#pragma once

#include <vector>
#include "../Edges.hpp"
#include "Graph.hpp"
#include "../Reachability.hpp"
#include "../Types.hpp"

namespace gracfl {
    /**
     * @class Graph3DOut
     * @brief A 3D graph structure that stores only outgoing edges for CFL reachability analysis.
     *
     * This class organizes outgoing edges by both labels and source nodes, enabling label-partitioned
     * graph traversal. It is optimized for forward grammar-driven CFL solving, allowing fast edge 
     * lookups and efficient memory usage for large graphs.
     */
    class Graph3DOut : public Graph
    {
    public:
        std::vector<std::vector<TemporalVector>> outEdges_;
        ReachabilityMatrix hashset_;
        
        Graph3DOut(std::string& graphfilepath, const Grammar& grammar);
        Graph3DOut(const std::vector<Edge>& edges, const Grammar& grammar);
        void initContainers();
        void addInitialEdges();
        void clearContainers();
        bool addInputEdge(const Edge& edge);
        void addSelfEdge(Edge& edge);
        bool checkAndAddEdge(const Edge& edge);
        ull countEdge();

        inline std::vector<std::vector<TemporalVector>>& getOutEdges() { return outEdges_; }
        inline ReachabilityMatrix& getHashset() { return hashset_; }
        inline const ReachabilityMatrix& getHashset() const { return hashset_; }
    };
}
