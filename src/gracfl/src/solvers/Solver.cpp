#include "utils/DebugLog.hpp"
#include <iostream>
#include <chrono>     
#include <stdexcept>  
#include <string> 
#include <map> 
#include "solvers/Solver.hpp"

namespace gracfl
{
    Solver::Solver(Config& config)
    : config_(config)
    , grammar_(new Grammar(config.grammarFilepath))  
    {
       solver_ = selectSolver();
       if (solver_ == nullptr)
       {
            throw std::runtime_error("Invalid Config!");
       }
    }

    Solver::~Solver()
    {
        delete grammar_;
    }

    SolverBase* Solver::selectSolver() 
    {
        if (config_.executionMode == "serial") {
            if (config_.traversalDirection == "fw") {
                if (config_.processingStrategy == "gram-driven") {
                    return new SolverFWGram(config_.graphFilepath, *grammar_);
                } else if (config_.processingStrategy == "topo-driven") {
                    return new SolverFWTopo(config_.graphFilepath, *grammar_);
                }
            }
            else if (config_.traversalDirection == "bw") {
                if (config_.processingStrategy == "gram-driven") {
                    return new SolverBWGram(config_.graphFilepath, *grammar_);
                } else if (config_.processingStrategy == "topo-driven") {
                    return new SolverBWTopo(config_.graphFilepath, *grammar_);
                }
            }
            else if (config_.traversalDirection == "bi") {
                if (config_.processingStrategy == "gram-driven") {
                    return new SolverBIGram(config_.graphFilepath, *grammar_);
                } else if (config_.processingStrategy == "topo-driven") {
                    return new SolverBITopo(config_.graphFilepath, *grammar_);
                }
            }                        
        } 
        else if (config_.executionMode == "parallel") {
            if (config_.traversalDirection == "fw") {
                if (config_.processingStrategy == "gram-driven") {
                    return new SolverFWGramParallel(config_.graphFilepath, *grammar_, config_.numThreads);
                } else if (config_.processingStrategy == "topo-driven") {
                    return new SolverFWTopoParallel(config_.graphFilepath, *grammar_, config_.numThreads);
                }
            }
            else if (config_.traversalDirection == "bw") {
                if (config_.processingStrategy == "gram-driven") {
                    return new SolverBWGramParallel(config_.graphFilepath, *grammar_, config_.numThreads);
                } else if (config_.processingStrategy == "topo-driven") {
                    return new SolverBWTopoParallel(config_.graphFilepath, *grammar_, config_.numThreads);
                }
            }
            else if (config_.traversalDirection == "bi") {
                if (config_.processingStrategy == "gram-driven") {
                    return new SolverBIGramParallel(config_.graphFilepath, *grammar_, config_.numThreads);
                } 
                else if (config_.processingStrategy == "topo-driven") {
                    return new SolverBITopoParallel(config_.graphFilepath, *grammar_, config_.numThreads);
                }
            }
        }
        return nullptr;
    }

    void Solver::solve()
    {
        ull initEdgeCnt = solver_->getEdgeCount();
        gracfl::dbg() << "---------------------------------------" << std::endl;
        gracfl::dbg() << "Start of the CFL Reachability Analysis" << std::endl;
        gracfl::dbg() << "---------------------------------------" << std::endl;
        std::chrono::time_point<std::chrono::steady_clock> start, finish;
        start = std::chrono::steady_clock::now();

        solver_->runCFL();

        finish = std::chrono::steady_clock::now();
        std::chrono::duration<double> elapsedSeconds = finish - start;

        gracfl::dbg() << "---------------------------------------" << std::endl;
        gracfl::dbg() << "End of the CFL Reachability Analysis" << std::endl;
        gracfl::dbg() << "---------------------------------------" << std::endl;

        ull newEdgeCnt = solver_->getEdgeCount() - initEdgeCnt;

        gracfl::dbg() << "---------------Results-----------------" << std::endl;
        gracfl::dbg() << "---------------------------------------" << std::endl;

        gracfl::dbg() << "Initial Edges\t= " << initEdgeCnt << std::endl;
        gracfl::dbg() << "New Edges\t= " << newEdgeCnt << std::endl;
        gracfl::dbg() << "Total Time\t= " << elapsedSeconds.count() << " seconds" << std::endl;

        gracfl::dbg() << "---------------END---------------------\n\n\n" << std::endl;
    }

    std::vector<std::vector<std::unordered_set<ull>>> Solver::getGraph()
    {
        return solver_->getGraph();
    }

    std::unordered_map<uint, std::string> Solver::getLabelIDToSymbolMap() const
    {
        return grammar_->getIDToSymbolMap();
    }

    void Solver::printLabelIDToSymbolMap() const
    {
        gracfl::dbg() << "---------------------------------------" << std::endl;
        gracfl::dbg() << "------- Label ID To Symbol Map --------" << std::endl;
        gracfl::dbg() << "---------------------------------------" << std::endl;

        const auto& idToSymbolMap = grammar_->getIDToSymbolMap();

        // copy into an ordered std::map
        std::map<uint, std::string> sortedMap(idToSymbolMap.begin(), idToSymbolMap.end());

        for (const auto& kv : sortedMap) {
            gracfl::dbg() << kv.first << "\t->\t" << kv.second << '\n';
        }

        gracfl::dbg()<<"\n";
    }
}