#include <iostream>
#include "solvers/SolverFWGram.hpp"

namespace gracfl 
{   
    SolverFWGram::SolverFWGram(std::string graphfilepath, Grammar& grammar)
    : grammar_(grammar)
    , graph_(new Graph3DOut(graphfilepath, grammar))
    {
    }

    SolverFWGram::SolverFWGram(std::vector<Edge>& edges, Grammar& grammar)
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
        bool terminate;
        auto& outEdges = graph_->outEdges_;
        auto& hashset = graph_->hashset_;
        auto& grammar2index = grammar_.grammar2index_;
        auto& grammar3indexLeft  = grammar_.grammar3indexLeft_;
        auto labelSize = grammar_.getLabelSize();
        auto nodeSize = graph_->getNodeSize();

        addSelfEdges(); // add epsilon edges
        do {
            itr++;
            terminate = true;
            runSingleIteration(
                outEdges,
                hashset, 
                grammar2index,
                grammar3indexLeft,
                labelSize,
                nodeSize,
                terminate);
            std::cout << "Iteration " << itr << std::endl;
        } while(!terminate);
    }

    void SolverFWGram::runSingleIteration(
        std::vector<std::vector<TemporalVector>>& outEdges,
        std::vector<std::vector<std::unordered_set<ull>>>& hashset,
        std::vector<std::vector<uint>>& grammar2index,
        std::vector<std::vector<std::pair<uint, uint>>>& grammar3indexLeft,
        uint labelSize,
        uint nodeSize,
        bool& terminate)
    {
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
                        graph_->checkAndAddEdge(newEdge, terminate);
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
                            graph_->checkAndAddEdge(newEdge, terminate);
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
                            graph_->checkAndAddEdge(newEdge, terminate);
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

    ull SolverFWGram::getEdgeCount()  
    { 
        return graph_->countEdge();
    };
}