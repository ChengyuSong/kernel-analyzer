#pragma once

#include "utils/graphs/Graph.hpp"
#include "utils/graphs/Graph3DOut.hpp"
#include "utils/Edges.hpp"
#include "utils/Types.hpp"
#include "utils/Config.hpp"
#include "utils/Grammar.hpp"
#include "utils/Reachability.hpp"
#include "solvers/SolverBase.hpp"

namespace gracfl 
{
    /**
     * @class SolverFWGram
     * @brief Forward traversal CFL reachability solver using a grammar-driven strategy.
     * 
     * This solver implements context-free language (CFL) reachability analysis by applying
     * grammar rules in a forward manner over a labeled graph structure.
     */
    class SolverFWGram : public SolverBase 
    {
    protected:
        const Grammar& grammar_;  ///< Reference to the grammar defining CFL rules.
        Graph3DOut* graph_; ///< Pointer to the graph structure supporting forward traversal.
    public:
        /**
         * @brief Constructs a SolverFWGram instance.
         * 
         * Initializes the solver with a graph loaded from the specified path and a reference to the grammar.
         * 
         * @param graphfilepath Path to the graph file.
         * @param grammar Reference to the Grammar object for rule-based traversal.
         */
        SolverFWGram(std::string graphfilepath, const Grammar& grammar);

        /**
         * @brief Constructs a SolverFWGram instance from edges.
         * 
         * @param edges Vector of edges to initialize the graph.
         * @param grammar Reference to the Grammar object for rule-based traversal.
         */
        SolverFWGram(const std::vector<Edge>& edges, const Grammar& grammar);

        /**
         * @brief Destructor for SolverFWGram.
         * 
         * Cleans up dynamically allocated graph memory.
         */
        ~SolverFWGram();

         /**
         * @brief Executes the main CFL solving loop until convergence is reached.
         */
        void runCFL() override;

        /**
         * @brief Performs a single iteration of the CFL reachability update.
         * 
         * Applies both unary and binary grammar rules to update the transitive reachability information.
         * 
         * @param outEdges Outgoing edges organized by label and source vertex.
         * @param hashset Data structure to store reachability results.
         * @param grammar2index Index-based access for unary grammar rules.
         * @param grammar3indexLeft Index-based access for binary grammar rules (left-child driven).
         * @param labelSize Number of unique grammar labels.
         * @param nodeSize Total number of nodes in the graph.
         * @return True if any new edges were added in this iteration.
         */
        bool runSingleIteration(
            std::vector<std::vector<TemporalVector>>& outEdges,
            const std::vector<std::vector<uint>>& grammar2index,
            const std::vector<std::vector<std::pair<uint, uint>>>& grammar3indexLeft,
            uint labelSize,
            uint nodeSize);

        /**
         * @brief Adds self-loop epsilon edges to support epsilon productions.
         */
        void addSelfEdges();

        std::vector<std::vector<std::unordered_set<ull>>> getGraph() override;

        // Preferred access for in-tree users: avoids materializing a huge copy.
        inline const ReachabilityMatrix& getReachability() const { return graph_->getHashset(); }

        /**
         * @brief Retrieves the total number of CFL-reachable edges in the graph.
         * @return Number of reachable edges.
         */
        ull getEdgeCount() override;
    };
}
