#pragma once

#include "utils/graphs/Graph.hpp"
#include "utils/graphs/Graph3DBiConcurrent.hpp"
#include "utils/Edges.hpp"
#include "utils/Types.hpp"
#include "utils/Config.hpp"
#include "utils/Grammar.hpp"
#include "solvers/SolverBase.hpp"

namespace gracfl 
{
    /**
     * @class SolverBIGramParallel
     * @brief Bidirectional grammar-driven parallel solver.
     *
     * This solver operates on a Graph3DBiConcurrent structure and uses grammar rules to perform
     * context-free language reachability analysis in both forward and backward directions.
     */
    class SolverBIGramParallel : public SolverBase
    {
        Grammar& grammar_; ///< Reference to the grammar rules used for CFL parsing.
        Graph3DBiConcurrent* graph_; ///< Pointer to the bidirectional graph structure.
        uint numOfThreads_;
    public:
        /**
         * @brief Constructor for SolverBIGramParallel.
         * @param graphfilepath Path to the input graph file.
         * @param grammar Reference to the Grammar object.
         */
        SolverBIGramParallel(std::string graphfilepath, Grammar& grammar, uint numOfThreads);
        SolverBIGramParallel(std::vector<Edge>& edges, Grammar& grammar, uint numOfThreads);

        /**
         * @brief Destructor.
         */
        ~SolverBIGramParallel();

        /**
         * @brief Executes the main CFL solving loop until convergence.
         */
        void runCFL() override;

        /**
         * @brief Runs a single iteration of the CFL solving process.
         *
         * Applies production rules using both incoming and outgoing edges to perform updates
         * to the graph via hashsets.
         *
         * @param outEdges Outgoing edge lists.
         * @param inEdges Incoming edge lists.
         * @param hashset Edge presence tracker (label × node → set of neighbors).
         * @param grammar2index Unary production rules.
         * @param grammar3indexLeft Binary productions (left-side association).
         * @param grammar3indexRight Binary productions (right-side association).
         * @param labelSize Number of total symbols.
         * @param nodeSize Total number of nodes/vertex in the graph.
         * @param terminate Flag indicating whether convergence has been reached.
         */

        void runSingleIterationParallel(
            std::vector<std::vector<TemporalVectorConcurrent>>& outEdges,
            std::vector<std::vector<TemporalVectorConcurrent>>& inEdges,
            std::vector<std::vector<tbb::concurrent_unordered_set<ull>>>& hashset,
            std::vector<std::vector<uint>>& grammar2index,
            std::vector<std::vector<std::pair<uint, uint>>>& grammar3indexLeft,
            std::vector<std::vector<std::pair<uint, uint>>>& grammar3indexRight,
            uint labelSize,
            uint nodeSize,
            bool& terminate);

        /**
         * @brief Adds self-loop epsilon edges to support epsilon productions.
         */
        void addSelfEdges();

        /**
         * @brief Returns the graph's final CFL-reachable edges.
         * @return Graph hashset (node × label → reachable destination node set).
         */
        std::vector<std::vector<std::unordered_set<ull>>> getGraph() override;

        /**
         * @brief Retrieves the total number of CFL-reachable edges in the graph.
         * @return Number of reachable edges.
         */
        ull getEdgeCount() override;
    };
}