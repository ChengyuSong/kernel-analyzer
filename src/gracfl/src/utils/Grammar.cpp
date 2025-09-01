#include <fstream>
#include <sstream>
#include <iostream> 
#include <stdexcept>
#include <cstdlib> 
#include "utils/Grammar.hpp"

namespace gracfl 
{
    Grammar::Grammar(const std::string& grammarFilePath) 
    {
        grammarFilePath_ = grammarFilePath;
        loadGrammarFile();

        grammar1index_.assign(labelSize_, false);
		grammar2index_.assign(labelSize_, {});
		grammar3index_.assign(labelSize_ * labelSize_, {});
		grammar3indexLeft_.assign(labelSize_, {});
		grammar3indexRight_.assign(labelSize_, {});

        for (int i = 0; i < grammar1_.size(); i++)
		{
			grammar1index_[grammar1_[i][0]] = true;
		}

        for (int i = 0; i < grammar2_.size(); i++)
		{
			grammar2index_[grammar2_[i][1]].push_back(grammar2_[i][0]);
		}

		for (int i = 0; i < grammar3_.size(); i++)
		{
			grammar3index_[grammar3_[i][1] * labelSize_ + grammar3_[i][2]].push_back(grammar3_[i][0]);
            grammar3indexLeft_[grammar3_[i][1]].push_back(std::make_pair(grammar3_[i][2], grammar3_[i][0]));
            grammar3indexRight_[grammar3_[i][2]].push_back(std::make_pair(grammar3_[i][1], grammar3_[i][0]));
		}
    }

    void Grammar::loadGrammarFile() 
    {
        std::ifstream grammarFile(grammarFilePath_);
        if (!grammarFile.is_open()) {
            throw std::runtime_error("Unable to open grammar file: " + grammarFilePath_);
        }

		std::string line;
		std::string symbol;
		int numSym;
		std::vector<uint> symbols;

		std::stringstream ss;
		labelSize_ = 0;
		while (getline(grammarFile, line))
		{
			ss.clear();
            symbols.clear();
			ss << line;
			numSym = 0;
			while (ss >> symbol)
			{
				if (hashSym_.count(symbol) <= 0)
				{
                    hashSym_[symbol] = labelSize_;
					hashSymRev_[labelSize_] = symbol;
                    allLabels_.insert(symbol);
					labelSize_++;
				}
				numSym++;
				symbols.push_back(hashSym_[symbol]); // pushing the index (here labelSize) of the symbol instead of the symbol itself
			}
            
			if (numSym == 1)
            {
				// grammar1[0][0] will return the index of the symbol. Then we can use it to get the
				// actual symbol from the hashSymRev
				grammar1_.push_back(symbols);
            }
			else if (numSym == 2)
            {
				grammar2_.push_back(symbols);
            }
			else if (numSym == 3)
            {
				grammar3_.push_back(symbols);
            }
			else
			{
				std::cout << "An error happened during parsing the grammar!\n";
				exit(0);
			}
		}

        grammarFile.close();
    }
}