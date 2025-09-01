#include <iostream>
#include "solvers/SolverBWGram.hpp"

namespace gracfl 
{
    SolverBWGram::SolverBWGram(std::string graphfilepath, Grammar& grammar)
    : grammar_(grammar)
    , graph_(new Graph3DIn(graphfilepath, grammar))
    {
    }

    SolverBWGram::SolverBWGram(std::vector<Edge>& edges, Grammar& grammar)
    : grammar_(grammar)
    , graph_(new Graph3DIn(edges, grammar))
    {
    }

    SolverBWGram::~SolverBWGram()
    {
        delete graph_;
    }

    void  SolverBWGram::runCFL()
    {
        uint itr = 0;
        bool terminate;
        auto& inEdges = graph_->inEdges_;
        auto& inHashset = graph_->inHashset_;
        auto& grammar2index = grammar_.grammar2index_;
        auto& grammar3indexRight = grammar_.grammar3indexRight_;
        auto labelSize = grammar_.getLabelSize();
        auto nodeSize = graph_->getNodeSize();

        addSelfEdges(); // add epsilon edges
        do {
            itr++;
            terminate = true;
            runSingleIteration(
                inEdges, 
                inHashset, 
                grammar2index,
                grammar3indexRight,
                labelSize,
                nodeSize,
                terminate);
            std::cout << "Iteration " << itr << std::endl;
        } while(!terminate);
    }

    void  SolverBWGram::runSingleIteration(
        std::vector<std::vector<TemporalVector>>& inEdges,
        std::vector<std::vector<std::unordered_set<ull>>>& inHashset,
        std::vector<std::vector<uint>>& grammar2index,
        std::vector<std::vector<std::pair<uint, uint>>>& grammar3indexRight,
        uint labelSize,
        uint nodeSize,
        bool& terminate
    )
    {
        for (uint i = 0; i < nodeSize; i++)
        {
            for (uint g = 0; g < labelSize; g++)
            {
                uint inNbr1;
                uint START_NEW = inEdges[i][g].OLD_END;
                uint END_NEW = inEdges[i][g].NEW_END;

                for (uint j = START_NEW; j < END_NEW; j++)
                {
                    inNbr1 = inEdges[i][g].vertexList[j];
                    
                    for (uint m = 0; m < grammar2index[g].size(); m++)
                    {
                        uint A = grammar2index[g][m];
                        Edge newEdge(inNbr1, i, A);
                        graph_->checkAndAddEdge(newEdge, terminate);
                    }

                    for (uint m = 0; m < grammar3indexRight[g].size(); m++)
                    {
                        uint B = grammar3indexRight[g][m].first;
                        uint A = grammar3indexRight[g][m].second;

                        uint START_OLD_OUT = 0;
                        uint END_NEW_OUT = inEdges[inNbr1][B].NEW_END;
                        for (uint h = START_OLD_OUT; h < END_NEW_OUT; h++)
                        {
                            uint inNbr2 = inEdges[inNbr1][B].vertexList[h];
                            Edge newEdge(inNbr2, i, A);
                            graph_->checkAndAddEdge(newEdge, terminate);
                        }
                    }
                }

                uint START_OLD = 0;
                uint END_OLD = inEdges[i][g].OLD_END;
                for (uint j = START_OLD; j < END_OLD; j++)
                {
                    inNbr1 = inEdges[i][g].vertexList[j];

                    for (uint m = 0; m < grammar3indexRight[g].size(); m++)
                    {
                        // C = g
                        uint B = grammar3indexRight[g][m].first;
                        uint A = grammar3indexRight[g][m].second;

                        uint START_NEW_OUT = inEdges[inNbr1][B].OLD_END;
                        uint END_NEW_OUT = inEdges[inNbr1][B].NEW_END;

                        for (uint h = START_NEW_OUT; h < END_NEW_OUT; h++)
                        {
                            uint inNbr2 = inEdges[inNbr1][B].vertexList[h];
                            Edge newEdge(inNbr2, i, A);
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
                inEdges[i][g].OLD_END = inEdges[i][g].NEW_END;
                inEdges[i][g].NEW_END = inEdges[i][g].vertexList.size();
            }
        }
    }
    

    void SolverBWGram::addSelfEdges()
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

    ull SolverBWGram::getEdgeCount()  
    { 
        return graph_->countEdge();
    };
}