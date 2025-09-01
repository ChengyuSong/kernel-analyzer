#include <iostream>
#include "solvers/SolverBITopoParallel.hpp"

namespace gracfl 
{
    static std::vector<std::vector<std::unordered_set<ull>>> to_std_hashset(
        const std::vector<std::vector<tbb::concurrent_unordered_set<ull>>>& 
        tbb_hashset)
    {
        std::vector<std::vector<std::unordered_set<ull>>> result;
        result.reserve(tbb_hashset.size());

        for (const auto& inner_cv : tbb_hashset) {
            // create a std::vector for this row
            std::vector<std::unordered_set<ull>> row;
            row.reserve(inner_cv.size());

            for (const auto& conc_set : inner_cv) {
                // copy all elements into a std::unordered_set
                std::unordered_set<ull> std_set(conc_set.begin(), conc_set.end());
                row.emplace_back(std::move(std_set));
            }

            result.emplace_back(std::move(row));
        }

        return result;
    }

    SolverBITopoParallel::SolverBITopoParallel(std::string graphfilepath, Grammar& grammar, uint numOfThreads)
    : grammar_(grammar)
    , graph_(new Graph2DBiConcurrent(graphfilepath, grammar))
    {
        numOfThreads_ = numOfThreads;
    }

    SolverBITopoParallel::SolverBITopoParallel(std::vector<Edge>& edges, Grammar& grammar, uint numOfThreads)
    : grammar_(grammar)
    , graph_(new Graph2DBiConcurrent(edges, grammar))
    {
        numOfThreads_ = numOfThreads;
    }

    SolverBITopoParallel::~SolverBITopoParallel()
    {
        delete graph_;
    }

    void  SolverBITopoParallel::runCFL()
    {
       
        uint itr = 0;
        bool terminate;
        auto& outEdges = graph_->outEdges_;
        auto& inEdges = graph_->inEdges_;
        auto& hashset = graph_->hashset_;
        auto& grammar2index = grammar_.grammar2index_;
        auto& grammar3index  = grammar_.grammar3index_;
        auto labelSize = grammar_.getLabelSize();
        auto nodeSize = graph_->getNodeSize();

        addSelfEdges(); // add epsilon edges
        do {
            itr++;
            terminate = true;
            runSingleIterationParallel(
                outEdges,
                inEdges, 
                hashset, 
                grammar2index,
                grammar3index,
                labelSize,
                nodeSize,
                terminate);
            std::cout << "Iteration " << itr << std::endl;
        } while(!terminate);
    }

    void SolverBITopoParallel::runSingleIterationParallel(
        std::vector<TemporalVectorConcurrentWithLbldVtx>& outEdges,
        std::vector<TemporalVectorConcurrentWithLbldVtx>& inEdges,
        std::vector<std::vector<tbb::concurrent_unordered_set<ull>>>& hashset,
        std::vector<std::vector<uint>>& grammar2index,
        std::vector<std::vector<uint>>& grammar3index,
        uint labelSize,
        uint nodeSize,
        bool& terminate)
    {
        // Derive new edges based on grammar rules
        #pragma omp parallel for schedule(static, 512) num_threads(numOfThreads_)
        for (uint i = 0; i < nodeSize; i++)
		{
			LbldVtx inNbr;
			uint START_NEW_IN = inEdges[i].OLD_END;
			uint END_NEW_IN = inEdges[i].NEW_END;

			// for each new edge
			for (uint j = START_NEW_IN; j < END_NEW_IN; j++)
			{
				inNbr = inEdges[i].vertexList[j];

				// ------- Rule Type: A = B -------
				std::vector<uint> leftLabels = grammar2index[inNbr.label];
				for (uint g = 0; g < leftLabels.size(); g++)
				{
                    Edge newEdge(inNbr.vtx, i, leftLabels[g]);
					graph_->checkAndAddEdge(newEdge, terminate);
				}

				// ------- Rule Type: A = BC -------
				uint START_OLD = 0;
				uint END_NEW = outEdges[i].NEW_END;
				for (uint h = START_OLD; h < END_NEW; h++)
				{
					LbldVtx outNbr = outEdges[i].vertexList[h];
					std::vector<uint> leftLabels = grammar3index[inNbr.label * labelSize + outNbr.label];
					for (uint g = 0; g < leftLabels.size(); g++)
					{
                        Edge newEdge(inNbr.vtx, outNbr.vtx, leftLabels[g]);
                        graph_->checkAndAddEdge(newEdge, terminate);
					}
				}
			}

			uint NEW_START_OUT = outEdges[i].OLD_END;
			uint NEW_END_OUT = outEdges[i].NEW_END;
			for (uint j = NEW_START_OUT; j < NEW_END_OUT; j++)
			{
				LbldVtx outNbr = outEdges[i].vertexList[j];

				// ------- Rule Type: A = CB -------
				uint OLD_START_IN = 0;
				uint OLD_END_IN = inEdges[i].OLD_END;
				for (uint h = OLD_START_IN; h < OLD_END_IN; h++)
				{
					LbldVtx inNbr = inEdges[i].vertexList[h];
					std::vector<uint> leftLabels = grammar3index[inNbr.label * labelSize + outNbr.label];

					for (uint g = 0; g < leftLabels.size(); g++)
					{
                        Edge newEdge(inNbr.vtx, outNbr.vtx, leftLabels[g]);
                        graph_->checkAndAddEdge(newEdge, terminate);
					}
				}
			}
		}

		 // ----------------- Update Sliding Pointers -----------------
        #pragma omp parallel for schedule(static, 512) num_threads(numOfThreads_)
		for (int i = 0; i < nodeSize; i++)
		{
			outEdges[i].OLD_END = outEdges[i].NEW_END;
			inEdges[i].OLD_END = inEdges[i].NEW_END;
			outEdges[i].NEW_END = outEdges[i].vertexList.size();
			inEdges[i].NEW_END = inEdges[i].vertexList.size();
		}
    }

    void SolverBITopoParallel::addSelfEdges()
    {
        for (int i = 0; i < graph_->getNodeSize(); i++)
        {
            for (int l = 0; l < grammar_.getRule1().size(); l++)
            {
                Edge edge(i, i, grammar_.grammar1_[l][0]);
                graph_->addSelfEdge(edge);
            }
        }
    }

    ull SolverBITopoParallel::getEdgeCount()  
    { 
        return graph_->countEdge();
    }

    std::vector<std::vector<std::unordered_set<ull>>> SolverBITopoParallel::getGraph() { 
        return to_std_hashset(graph_->getHashset()); 
    }
}