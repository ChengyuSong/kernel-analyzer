#include "utils/DebugLog.hpp"
#include <iostream>
#include "solvers/SolverFWGram.hpp"

namespace gracfl 
{   
    SolverFWGram::SolverFWGram(std::string graphfilepath, const Grammar& grammar)
    : grammar_(grammar)
    , graph_(new Graph3DOut(graphfilepath, grammar))
    {
    }

    SolverFWGram::SolverFWGram(const std::vector<Edge>& edges, const Grammar& grammar)
    : grammar_(grammar)
    , graph_(new Graph3DOut(edges, grammar))
    {
    }

    SolverFWGram::~SolverFWGram()
    {
        delete graph_;
    }

    void  SolverFWGram::runCFL()
    { 
        uint itr = 0;
        auto& outEdges = graph_->outEdges_;
        auto& hashset = graph_->hashset_;
        auto& grammar2index = grammar_.grammar2index_;
        auto& grammar3indexLeft  = grammar_.grammar3indexLeft_;
        auto labelSize = grammar_.getLabelSize();
        auto nodeSize = graph_->getNodeSize();

        ensureSelfEdges();
        bool changed;
        do {
            itr++;
            changed = runSingleIteration(
                outEdges,
                grammar2index,
                grammar3indexLeft,
                labelSize,
                nodeSize);
            gracfl::dbg() << "Iteration " << itr << std::endl;
        } while(changed);
    }

    bool SolverFWGram::runSingleIteration(
        std::vector<std::vector<TemporalVector>>& outEdges,
        const std::vector<std::vector<uint>>& grammar2index,
        const std::vector<std::vector<std::pair<uint, uint>>>& grammar3indexLeft,
        uint labelSize,
        uint nodeSize)
    {
        bool changed = false;
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
                        changed |= graph_->checkAndAddEdge(newEdge);
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
                            changed |= graph_->checkAndAddEdge(newEdge);
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
                            changed |= graph_->checkAndAddEdge(newEdge);
                        }
                    }
                }
            }
        }

        // ----------------- Update Sliding Pointers -----------------
        for (uint i = 0; i < nodeSize; i++)
        {
            for (uint g = 0; g < labelSize; g++)
            {
                outEdges[i][g].OLD_END = outEdges[i][g].NEW_END;
                outEdges[i][g].NEW_END = outEdges[i][g].vertexList.size();
            }
        }

        return changed;
    }

    void SolverFWGram::addSelfEdges()
    {
        for (uint i = 0; i < graph_->getNodeSize(); i++)
        {
            for (uint l = 0; l < grammar_.getRule1().size(); l++)
            {
                Edge edge(i, i, grammar_.getRule1()[l][0]);
                graph_->addSelfEdge(edge);
            }
        }
    }

    void SolverFWGram::ensureSelfEdges()
    {
        if (selfEdgesInitialized_) {
            return;
        }
        addSelfEdges();
        selfEdgesInitialized_ = true;
    }

    size_t SolverFWGram::addInputEdges(const std::vector<Edge>& edges, size_t beginIndex)
    {
        if (beginIndex >= edges.size()) {
            return 0;
        }

        size_t added = 0;
        for (size_t i = beginIndex; i < edges.size(); i++) {
            if (graph_->addInputEdge(edges[i])) {
                added++;
            }
        }
        return added;
    }

    ull SolverFWGram::getEdgeCount()  
    { 
        return graph_->countEdge();
    };

    std::vector<std::vector<std::unordered_set<ull>>> SolverFWGram::getGraph()
    {
        const auto& hs = graph_->getHashset();
        std::vector<std::vector<std::unordered_set<ull>>> result;
        result.resize(hs.size());

        for (size_t i = 0; i < hs.size(); i++)
        {
            result[i].resize(hs[i].size());
            for (size_t j = 0; j < hs[i].size(); j++)
            {
                // Note: This can be very large. Prefer getReachability().
                result[i][j].insert(hs[i][j].begin(), hs[i][j].end());
            }
        }
        return result;
    }
} 
