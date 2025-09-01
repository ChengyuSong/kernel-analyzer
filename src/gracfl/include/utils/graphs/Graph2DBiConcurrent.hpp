#pragma once

#include <vector>
#include <unordered_set>
#include "../Edges.hpp"
#include "Graph.hpp"
#include "../Types.hpp"
#include "tbb/concurrent_vector.h"
#include "tbb/concurrent_queue.h"
#include "tbb/concurrent_unordered_set.h"

namespace gracfl {
    /**
     * @class Graph2DBiConcurrent
     * @brief A bidirectional graph structure for context-free language (CFL) reachability analysis.
     *
     * This class implements a 2D bidirectional graph where both incoming and outgoing edges are stored 
     * separately with associated labels. It provides mechanisms for initializing containers, adding edges, 
     * and tracking edge presence using hash sets. It is particularly suited for CFL-reachability solvers.
     */
    class Graph2DBiConcurrent : public Graph
    {
    public:
        std::vector<TemporalVectorConcurrentWithLbldVtx> outEdges_;
        std::vector<TemporalVectorConcurrentWithLbldVtx> inEdges_;
        std::vector<std::vector<tbb::concurrent_unordered_set<ull>>> hashset_;

        Graph2DBiConcurrent(std::string& graphfilepath, const Grammar& grammar);
        Graph2DBiConcurrent(std::vector<Edge>& edges, const Grammar& grammar);
        void initContainers();
        void addInitialEdges();
        void clearContainers();
        void addSelfEdge(Edge& edge);
        void checkAndAddEdge(Edge& edge, bool& terminate);
        ull countEdge();

        inline std::vector<TemporalVectorConcurrentWithLbldVtx>& getOutEdges()  { return outEdges_; }
        inline std::vector<TemporalVectorConcurrentWithLbldVtx>& getInEdges() { return inEdges_; }
        inline std::vector<std::vector<tbb::concurrent_unordered_set<ull>>>& getHashset() { return hashset_; }
    };
}