#ifndef STRUCT_ANALYZER_H
#define STRUCT_ANALYZER_H

#include <llvm/IR/Module.h>
#include <llvm/IR/Type.h>
#include <llvm/ADT/iterator_range.h>
#include <llvm/Support/raw_ostream.h>

#include <vector>
#include <set>
#include <unordered_map>

// Every struct type T is mapped to the vectors fieldSize and offsetMap.
// If field [i] in the expanded struct T begins an embedded struct, fieldSize[i] is the # of fields in the largest such struct, else S[i] = 1.
// Also, if a field has index (j) in the original struct, it has index offsetMap[j] in the expanded struct.
class StructInfo
{
private:
	std::vector<bool> arrayFlags; // true if field is an array
	std::vector<bool> pointerFlags; // true if field is a pointer
	std::vector<bool> unionFlags; // true if field is a union
	std::vector<unsigned> fieldSize;
	std::vector<unsigned> offsetMap; // field index to expanded field index
	std::vector<unsigned> fieldOffset; // expanded field index => offset in bytes
	std::vector<unsigned> fieldRealSize; // expanded field index => allocation size in bytes

	// field => type(s) map, stripping off arrays
	std::unordered_map<unsigned, std::set<const llvm::Type*> > elementType;
	
	// the corresponding data layout for this struct
	const llvm::DataLayout* dataLayout;
	void setDataLayout(const llvm::DataLayout* layout) { dataLayout = layout; }

	// real type definition
	const llvm::StructType* stType;
	void setRealType(const llvm::StructType* st) { stType = st; }

	// defining module
	const llvm::Module* module;
	void setModule(const llvm::Module* M) { module = M; }

	// container type(s), i.e., the struct(s) that contain this struct at the specified offset
	std::unordered_map<const llvm::StructType*, std::set<unsigned>> containers;
	void addContainer(const llvm::StructType* st, unsigned offset)
	{
		containers[st].insert(offset);
	}

	static const llvm::StructType* maxStruct;
	static unsigned maxStructSize;
	uint64_t allocSize;

	bool finalized;

	void addOffsetMap(unsigned newOffsetMap) { offsetMap.push_back(newOffsetMap); }
	void addField(unsigned newFieldSize, bool isArray, bool isPointer, bool isUnion)
	{
		fieldSize.push_back(newFieldSize);
		arrayFlags.push_back(isArray);
		pointerFlags.push_back(isPointer);
		unionFlags.push_back(isUnion);
	}
	void addFieldOffset(unsigned newOffset) { fieldOffset.push_back(newOffset); }
	void addRealSize(unsigned size) { fieldRealSize.push_back(size); }
	void appendFields(const StructInfo& other)
	{
		if (!other.isEmpty()) {
			fieldSize.insert(fieldSize.end(), (other.fieldSize).begin(), (other.fieldSize).end());
		}
		arrayFlags.insert(arrayFlags.end(), (other.arrayFlags).begin(), (other.arrayFlags).end());
		pointerFlags.insert(pointerFlags.end(), (other.pointerFlags).begin(), (other.pointerFlags).end());
		unionFlags.insert(unionFlags.end(), (other.unionFlags).begin(), (other.unionFlags).end());
		fieldRealSize.insert(fieldRealSize.end(), (other.fieldRealSize).begin(), (other.fieldRealSize).end());
	}
	void appendFieldOffset(const StructInfo& other)
	{
		// The caller's addFieldOffset entry covers the sub-struct's expanded
		// field 0 (always at sub-offset 0), so skip exactly that first entry.
		// Skipping *by index* (not by value) keeps alignment when the sub has
		// several zero-size members at offset 0.
		unsigned base = fieldOffset.back();
		for (size_t i = 1; i < other.fieldOffset.size(); ++i)
			fieldOffset.push_back(other.fieldOffset[i] + base);
	}
	void addElementType(unsigned field, const llvm::Type* type) { elementType[field].insert(type); }
	void appendElementType(const StructInfo& other, unsigned base)
	{
		// `base` is the sub-struct's first expanded index in this struct; it
		// must be passed in because appendFields may already have grown the
		// flag vectors past it.
		for (auto item : other.elementType)
			elementType[item.first + base].insert(item.second.begin(), item.second.end());
	}

	// Must be called after all fields have been analyzed
	void finalize()
	{
		assert(fieldSize.size() == arrayFlags.size());
		assert(pointerFlags.size() == arrayFlags.size());
		assert(unionFlags.size() == arrayFlags.size());
		unsigned numField = fieldSize.size();
		if (numField == 0)
			fieldSize.resize(1);
		fieldSize[0] = numField;
		if (stType->isSized())
			allocSize = dataLayout->getTypeAllocSize(const_cast<llvm::StructType*>(stType));
		else
			allocSize = 0;
		finalized = true;
	}

	static void updateMaxStruct(const llvm::StructType* st, unsigned structSize)
	{
		if (structSize > maxStructSize) {
			maxStruct = st;
			maxStructSize = structSize;
		}
	}
public:
	bool isFinalized() {
		return finalized;
	}

	// # fields == # arrayFlags == # pointer flags
	// size => # of fields????
	// getExpandedSize => # of unrolled fields???

	typedef std::vector<unsigned>::const_iterator const_iterator;
	unsigned getSize() const { return offsetMap.size(); }
	unsigned getExpandedSize() const { return arrayFlags.size(); }

	bool isEmpty() const { return (fieldSize[0] == 0);}
	bool isFieldArray(unsigned field) const { return arrayFlags.at(field); }
	bool isFieldPointer(unsigned field) const { return pointerFlags.at(field); }
	bool isFieldUnion(unsigned field) const { return unionFlags.at(field); }
	unsigned getOffset(unsigned off) const { return offsetMap.at(off); }
	const llvm::Module* getModule() const { return module; }
	const llvm::DataLayout* getDataLayout() const { return dataLayout; }
	const llvm::StructType* getRealType() const { return stType; }
	const uint64_t getAllocSize() const { return allocSize; }
	unsigned getFieldRealSize(unsigned field) const { return fieldRealSize.at(field); }
	unsigned getFieldOffset(unsigned field) const { return fieldOffset.at(field); }
	// Per-expanded-slot vector sizes, exposed for invariant checking/tests.
	// Both must always equal getExpandedSize().
	unsigned getNumFieldOffsets() const { return fieldOffset.size(); }
	unsigned getNumFieldRealSizes() const { return fieldRealSize.size(); }
	std::set<const llvm::Type*> getElementType(unsigned field) const
	{
		auto itr = elementType.find(field);
		if (itr != elementType.end())
			return itr->second;
		else
			return std::set<const llvm::Type*>();
	}
	const llvm::StructType* getContainer(const llvm::StructType* st, unsigned offset) const
	{
		assert(!st->isOpaque());
		auto it = containers.find(st);
		if (it != containers.end() && it->second.count(offset))
			return st;
		return nullptr;
	}

	static unsigned getMaxStructSize() { return maxStructSize; }

	friend class StructAnalyzer;
};

// Construct the necessary StructInfo from LLVM IR
// This pass will make GEP instruction handling easier
class StructAnalyzer
{
private:
	// Map llvm type to corresponding StructInfo
	typedef std::unordered_map<const llvm::StructType*, StructInfo> StructInfoMap;
	StructInfoMap structInfoMap;

	// Map struct name to llvm type
	typedef std::unordered_map<std::string, const llvm::StructType*> StructMap;
	StructMap structMap;

	// Expand (or flatten) the specified StructType and produce StructInfo
	StructInfo& addStructInfo(const llvm::StructType* st, const llvm::Module* M, const llvm::DataLayout* layout);
	// If st has been calculated before, return its StructInfo; otherwise, calculate StructInfo for st
	StructInfo& computeStructInfo(const llvm::StructType* st, const llvm::Module *M, const llvm::DataLayout* layout);
	// update container information
	void addContainer(const llvm::StructType* container, StructInfo& containee, unsigned offset, const llvm::Module* M);
public:
	StructAnalyzer() = default;

	// Return NULL if info not found
	const StructInfo* getStructInfo(const llvm::StructType* st, llvm::Module* M) const;
	size_t getSize() const { return structMap.size(); }
	bool getContainer(std::string stid, const llvm::Module* M, std::set<std::string> &out) const;
	//bool getContainer(const llvm::StructType* st, std::set<std::string> &out) const;

	void run(llvm::Module* M, const llvm::DataLayout* layout);

	void printStructInfo() const;
	void printStructInfo(const StructInfo &info) const;
};

#endif
