#include <iostream>
#include "solvers/SolverBIGram.hpp"

namespace gracfl 
{
    SolverBIGram::SolverBIGram(std::string graphfilepath, Grammar& grammar)
    : grammar_(grammar)
    , graph_(new Graph3DBi(graphfilepath, grammar))
    {
    }

    SolverBIGram::SolverBIGram(std::vector<Edge>& edges, Grammar& grammar)
    : grammar_(grammar)
    , graph_(new Graph3DBi(edges, grammar))
    {
    }

    SolverBIGram::~SolverBIGram()
    {
        delete graph_;
    }

    void  SolverBIGram::runCFL()
    {
       
        uint itr = 0;
        bool terminate;
        auto& outEdges = graph_->outEdges_;
        auto& inEdges = graph_->inEdges_;
        auto& hashset = graph_->hashset_;
        auto& grammar2index = grammar_.grammar2index_;
        auto& grammar3indexLeft  = grammar_.grammar3indexLeft_;
        auto& grammar3indexRight = grammar_.grammar3indexRight_;
        auto labelSize = grammar_.getLabelSize();
        auto nodeSize = graph_->getNodeSize();

        addSelfEdges(); // add epsilon edges
        do {
            itr++;
            terminate = true;
            runSingleIteration(
                outEdges,
                inEdges, 
                hashset, 
                grammar2index,
                grammar3indexLeft,
                grammar3indexRight,
                labelSize,
                nodeSize,
                terminate);
            std::cout << "Iteration " << itr << std::endl;
        } while(!terminate);
    }


    void SolverBIGram::runSingleIteration(
        std::vector<std::vector<TemporalVector>>& outEdges,
        std::vector<std::vector<TemporalVector>>& inEdges,
        std::vector<std::vector<std::unordered_set<ull>>>& hashset,
        std::vector<std::vector<uint>>& grammar2index,
        std::vector<std::vector<std::pair<uint, uint>>>& grammar3indexLeft,
        std::vector<std::vector<std::pair<uint, uint>>>& grammar3indexRight,
        uint labelSize,
        uint nodeSize,
        bool& terminate)
    {
        // Derive new edges based on grammar rules  
        for (uint i = 0; i < nodeSize; i++)
        {
            for (uint g = 0; g < labelSize; g++)
            {
                uint nbr;
                uint START_NEW = inEdges[i][g].OLD_END;
                uint END_NEW = inEdges[i][g].NEW_END;
            
                // Process new in-edges labeled g
                for (uint j = START_NEW; j < END_NEW; j++)
                {
                    uint inNbr = inEdges[i][g].vertexList[j];

                    // ------- Rule Type: A = B -------
                    for (uint m = 0; m < grammar2index[g].size(); m++)
                    {
                        uint A = grammar2index[g][m];
                        Edge newEdge(inNbr, i, A);
                        graph_->checkAndAddEdge(newEdge, terminate);
                    }

                    // ------- Rule Type: A = BC -------
                    for (uint m = 0; m < grammar3indexLeft[g].size(); m++)
                    {
                        uint C = grammar3indexLeft[g][m].first;
                        uint A = grammar3indexLeft[g][m].second;

                        uint START_OLD_OUT = 0;
                        uint END_NEW_OUT = outEdges[i][C].NEW_END;
                        for (uint h = START_OLD_OUT; h < END_NEW_OUT; h++)
                        {
                            uint nbr = outEdges[i][C].vertexList[h];
                            Edge newEdge(inNbr, nbr, A);
                            graph_->checkAndAddEdge(newEdge, terminate);
                        }
                    }
                }


                uint START_NEW_OUT = outEdges[i][g].OLD_END;
                uint END_NEW_OUT = outEdges[i][g].NEW_END;
                // Process new out-edges labeled g
                for (uint j = START_NEW_OUT; j < END_NEW_OUT; j++)
                {   
                    uint nbr = outEdges[i][g].vertexList[j];

                    // ------- Rule Type 3: A = CB -------
                    for (uint m = 0; m < grammar3indexRight[g].size(); m++)
                    {
                        uint C = grammar3indexRight[g][m].first;
                        uint A = grammar3indexRight[g][m].second;

                        uint START_OLD_IN = 0;
                        uint END_OLD_IN = inEdges[i][C].OLD_END;
                        for (uint h = START_OLD_IN; h < END_OLD_IN; h++)
                        {
                            uint inNbr = inEdges[i][C].vertexList[h];
                            Edge newEdge(inNbr, nbr, A);
                            graph_->checkAndAddEdge(newEdge, terminate);
                        }
                    }
                }
            }
        }

        // Update sliding pointers for next iteration
        for (uint i = 0; i < nodeSize; i++)
        {
            for (uint g = 0; g < labelSize; g++)
            {
                outEdges[i][g].OLD_END = outEdges[i][g].NEW_END;
                outEdges[i][g].NEW_END = outEdges[i][g].vertexList.size();
                inEdges[i][g].OLD_END = inEdges[i][g].NEW_END; 
                inEdges[i][g].NEW_END = inEdges[i][g].vertexList.size();
            }
        }
    }

    void SolverBIGram::addSelfEdges()
    {
        for (uint i = 0; i < graph_->getNodeSize(); i++)
        {
            for (uint l = 0; l < grammar_.getRule1().size(); l++)
            {
                Edge edge(i, i, grammar_.grammar1_[l][0]);
                graph_->addSelfEdge(edge);
            }
        }
    }

    ull SolverBIGram::getEdgeCount()  
    { 
        return graph_->countEdge();
    }
}