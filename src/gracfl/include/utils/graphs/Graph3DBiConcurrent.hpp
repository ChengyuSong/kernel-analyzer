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
     * @class Graph3DBiConcurrent
     * @brief A 3D bidirectional graph structure for CFL reachability analysis with tbb concurrent datastructures
     *
     * This class represents a graph where edges are grouped by both source/destination nodes and labels,
     * allowing label-sensitive traversal in both forward and backward directions. It is suited for
     * grammar-driven and label-partitioned CFL solvers.
     */
    class Graph3DBiConcurrent : public Graph
    {
    public:
        std::vector<std::vector<TemporalVectorConcurrent>> outEdges_;
        std::vector<std::vector<TemporalVectorConcurrent>> inEdges_;
        std::vector<std::vector<tbb::concurrent_unordered_set<ull>>> hashset_;

        Graph3DBiConcurrent(std::string& graphfilepath, const Grammar& grammar);
        Graph3DBiConcurrent(std::vector<Edge>& edges, const Grammar& grammar);
        void initContainers();
        void addInitialEdges();
        void clearContainers();
        void addSelfEdge(Edge& edge);
        void checkAndAddEdge(Edge& edge, bool& terminate);
        ull countEdge();

        inline std::vector<std::vector<TemporalVectorConcurrent>>& getOutEdges()  { return outEdges_; }
        inline std::vector<std::vector<TemporalVectorConcurrent>>& getInEdges() { return inEdges_; }
        inline std::vector<std::vector<tbb::concurrent_unordered_set<ull>>>& getHashset() { return hashset_; }
    };
}
