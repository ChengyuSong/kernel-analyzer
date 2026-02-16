#include <iostream>
#include <chrono>
#include "solvers/SolverFWGramParallel.hpp"
#include "utils/Stats.hpp"

namespace gracfl 
{
    static ull count_total_edges(const std::vector<std::vector<TemporalVector>>& outEdges)
    {
        ull total = 0;
        for (size_t i = 0; i < outEdges.size(); i++) {
            for (size_t g = 0; g < outEdges[i].size(); g++) {
                total += outEdges[i][g].vertexList.size();
            }
        }
        return total;
    }

    // After sliding pointers are updated, NEW_END - OLD_END is exactly the
    // "frontier" (edges discovered in the last iteration).
    static ull count_frontier_edges(const std::vector<std::vector<TemporalVector>>& outEdges)
    {
        ull frontier = 0;
        for (size_t i = 0; i < outEdges.size(); i++) {
            for (size_t g = 0; g < outEdges[i].size(); g++) {
                const auto& tv = outEdges[i][g];
                frontier += static_cast<ull>(tv.NEW_END) - static_cast<ull>(tv.OLD_END);
            }
        }
        return frontier;
    }

    SolverFWGramParallel::SolverFWGramParallel(std::string graphfilepath, const Grammar& grammar, uint numOfThreads)
    : SolverFWGram(graphfilepath, grammar)
    {
        numOfThreads_ = numOfThreads;
    }

    SolverFWGramParallel::SolverFWGramParallel(const std::vector<Edge>& edges, const Grammar& grammar, uint numOfThreads)
    : SolverFWGram(edges, grammar)
    {
        numOfThreads_ = numOfThreads;
    }

    void  SolverFWGramParallel::runCFL()
    { 
        uint itr = 0;
        bool terminate;
        auto& outEdges = graph_->outEdges_;
        auto& grammar2index = grammar_.grammar2index_;
        auto& grammar3indexLeft  = grammar_.grammar3indexLeft_;
        auto labelSize = grammar_.getLabelSize();
        auto nodeSize = graph_->getNodeSize();

        const bool enableStats = stats::getenv_bool("GRACFL_STATS", false);
        const int statsInterval = std::max(1, stats::getenv_int("GRACFL_STATS_INTERVAL", 1));
        const bool deepStats = stats::getenv_bool("GRACFL_STATS_DEEP", false);

        addSelfEdges(); // add epsilon edges

        if (enableStats) {
            const double rssMb = stats::rss_kb() / 1024.0;
            std::cout << "[GraCFL] FWGramParallel threads=" << numOfThreads_
                      << " reachability=" << kReachabilitySetKind
                      << " nodes=" << nodeSize
                      << " labels=" << labelSize
                      << " rss_mb=" << rssMb;
            if (deepStats) {
                const ull initOut = count_total_edges(outEdges);
                const ull initSet = graph_->countEdge();
                std::cout << " initial_out=" << initOut
                          << " initial_set=" << initSet;
            }
            std::cout
                      << std::endl;
        }

        do {
            itr++;
            const auto t0 = std::chrono::steady_clock::now();
            runSingleIterationParallel(
                outEdges,
                grammar2index,
                grammar3indexLeft,
                labelSize,
                nodeSize);
            const auto t1 = std::chrono::steady_clock::now();

            const ull frontierEdges = count_frontier_edges(outEdges);
            terminate = (frontierEdges == 0);

            if (enableStats && (itr % static_cast<uint>(statsInterval) == 0 || terminate)) {
                const double rssMb = stats::rss_kb() / 1024.0;
                const double iterSec = std::chrono::duration<double>(t1 - t0).count();
                std::cout << "[GraCFL] itr=" << itr
                          << " +edges=" << frontierEdges
                          << " rss_mb=" << rssMb
                          << " iter_s=" << iterSec;
                if (deepStats) {
                    const ull totalOut = count_total_edges(outEdges);
                    const ull totalSet = graph_->countEdge();
                    std::cout << " total_out=" << totalOut
                              << " total_set=" << totalSet;
                }
                std::cout << std::endl;
            } else {
                std::cout << "Iteration " << itr << std::endl;
            }
        } while(!terminate);
    }

    void SolverFWGramParallel::runSingleIterationParallel(
        std::vector<std::vector<TemporalVector>>& outEdges,
        const std::vector<std::vector<uint>>& grammar2index,
        const std::vector<std::vector<std::pair<uint, uint>>>& grammar3indexLeft,
        uint labelSize,
        uint nodeSize)
    {
        #pragma omp parallel for schedule(static, 512) num_threads(numOfThreads_)
        for (uint i = 0; i < nodeSize; i++)
        {
            for (uint g = 0; g < labelSize; g++)
            {
                uint nbr;
                uint START_NEW = outEdges[i][g].OLD_END;
                uint END_NEW = outEdges[i][g].NEW_END;

                for (uint j = START_NEW; j < END_NEW; j++)
                {
                    nbr = outEdges[i][g].vertexList[j];
                    for (uint m = 0; m < grammar2index[g].size(); m++)
                    {
                        uint A = grammar2index[g][m];
                        Edge newEdge(i, nbr, A);
                        graph_->checkAndAddEdge(newEdge);
                    }

                    for (uint m = 0; m < grammar3indexLeft[g].size(); m++)
                    {
                        uint C = grammar3indexLeft[g][m].first;
                        uint A = grammar3indexLeft[g][m].second;

                        uint START_OLD_OUT = 0;
                        uint END_NEW_OUT = outEdges[nbr][C].NEW_END;
                        for (uint h = START_OLD_OUT; h < END_NEW_OUT; h++)
                        {
                            uint outNbr = outEdges[nbr][C].vertexList[h];
                            Edge newEdge(i, outNbr, A);
                            graph_->checkAndAddEdge(newEdge);
                        }
                    }
                }

                uint START_OLD = 0;
                uint END_OLD = outEdges[i][g].OLD_END;
                for (uint j = START_OLD; j < END_OLD; j++)
                {
                    nbr = outEdges[i][g].vertexList[j];
                    for (uint m = 0; m < grammar3indexLeft[g].size(); m++)
                    {
                        uint C = grammar3indexLeft[g][m].first;
                        uint A = grammar3indexLeft[g][m].second;

                        uint START_NEW_OUT = outEdges[nbr][C].OLD_END;
                        uint END_NEW_OUT = outEdges[nbr][C].NEW_END;
                        for (uint h = START_NEW_OUT; h < END_NEW_OUT; h++)
                        {
                            uint outNbr = outEdges[nbr][C].vertexList[h];
                            Edge newEdge(i, outNbr, A);
                            graph_->checkAndAddEdge(newEdge);
                        }
                    }
                }
            }
        }

        // ----------------- Update Sliding Pointers -----------------
        #pragma omp parallel for schedule(static) num_threads(numOfThreads_)
        for (uint i = 0; i < nodeSize; i++)
        {
            for (uint g = 0; g < labelSize; g++)
            {
                outEdges[i][g].OLD_END = outEdges[i][g].NEW_END;
                outEdges[i][g].NEW_END = outEdges[i][g].vertexList.size();
            }
        }
    }

    void SolverFWGramParallel::addSelfEdgesParallel()
    {
        #pragma omp parallel for schedule(static, 512) num_threads(numOfThreads_)
        for (uint i = 0; i < graph_->getNodeSize(); i++)
        {
            for (uint l = 0; l < grammar_.getRule1().size(); l++)
            {
                Edge edge(i, i, grammar_.getRule1()[l][0]);
                graph_->addSelfEdge(edge);
            }
        }
    }
}
