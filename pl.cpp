#include "pl.h"
#include <bitset>

CNF const operator|( Literal const& op1, Literal const& op2 ) { return CNF(op1)|CNF(op2); }
CNF const operator|( Literal const& op1, CNF     const& op2 ) { return CNF(op1)|op2; }
CNF const operator&( Literal const& op1, Literal const& op2 ) { return CNF(op1)&CNF(op2); }
CNF const operator&( Literal const& op1, CNF     const& op2 ) { return CNF(op1)&op2; }
CNF const operator>( Literal const& op1, Literal const& op2 ) { return CNF(op1)>CNF(op2); }
CNF const operator>( Literal const& op1, CNF     const& op2 ) { return CNF(op1)>op2; }


KnowledgeBase::KnowledgeBase() : clauses() {}
////////////////////////////////////////////////////////////////////////////
KnowledgeBase& KnowledgeBase::operator+=( CNF const& cnf ) {
	clauses.insert(cnf.begin(), cnf.end());
   /* for ( ClauseSet::const_iterator it = cnf.begin(); it != cnf.end(); ++it ) {
        clauses.insert( *it );
    }*/
    return *this;
}
KnowledgeBase & KnowledgeBase::operator+=(Literal const & literal)
{
	CNF cnf = literal;
	return (*this += cnf);
}
KnowledgeBase & KnowledgeBase::operator+=(KnowledgeBase const & kb)
{
	clauses.insert(kb.begin(), kb.end());
	/*for (ClauseSet::const_iterator it = kb.begin(); it != kb.end(); ++it) {
		clauses.insert(*it);
	}*/
	return *this;
}
KnowledgeBase & KnowledgeBase::operator+=(Clause const & clause)
{
	clauses.insert(clause);
	return *this;
}
////////////////////////////////////////////////////////////////////////
ClauseSet::const_iterator KnowledgeBase::begin() const { return clauses.begin(); }
ClauseSet::const_iterator KnowledgeBase::end()   const { return clauses.end(); }
unsigned                           KnowledgeBase::size()  const { return clauses.size(); }
////////////////////////////////////////////////////////////////////////////
bool KnowledgeBase::ProveByRefutation( CNF const& alpha ) const {

	CNF negatedAlpha = ~alpha;
	if (negatedAlpha.size() == 0) { // Every value is complimentary of each other, i.e. negate is always false
		return true;
	}
	KnowledgeBase intermediateKnowledgeBase(*this);
	// Remove original couples that result in true
	// They won't effect the process, they're just extra data from the viewpoint of resolution
	//intermediateKnowledgeBase.PurgeAbsoluteTruths();
	intermediateKnowledgeBase += negatedAlpha;
	KnowledgeBase processedKB;
	return ResolveKB(processedKB, intermediateKnowledgeBase);
}
bool KnowledgeBase::ResolveKB(KnowledgeBase & processedKB, KnowledgeBase & newKB) const
{
	// KB to be added to the original one
	KnowledgeBase additionalKnowledgeBase;

	// Process old data with new ones
	ClauseSet::const_iterator kbCurrentProcessed = processedKB.clauses.begin();
	ClauseSet::const_iterator kbEndProcessed = processedKB.clauses.end();
	ClauseSet::const_iterator kbCurrentNew;
	ClauseSet::const_iterator kbEndNew = newKB.clauses.end();
	while (kbCurrentProcessed != kbEndProcessed) {
		kbCurrentNew = newKB.clauses.begin();
		while (kbCurrentNew != kbEndNew) {
			Clause newClause = *kbCurrentProcessed | *(kbCurrentNew++);

			// If the new clause is an empty one => contradiction
			if (newClause.size() == 0) {
				return true;
			}
			// if the new clause doesn't exist in the set, add it to the addition KB
			else if (processedKB.clauses.find(newClause) == processedKB.clauses.end() 
				&& newKB.clauses.find(newClause) == newKB.clauses.end()) {
				additionalKnowledgeBase += newClause;
			}
		}
		++kbCurrentProcessed;
	}

	// Process new data among itself
	kbCurrentNew = newKB.clauses.begin();
	while (kbCurrentNew != kbEndNew) {
		// kbIterator starts from kbCurrent+1 to end for the rest of clauses in KB
		ClauseSet::const_iterator kbIterator = kbCurrentNew;
		++kbIterator;
		while (kbIterator != kbEndNew) { //go through all the other clauses
			Clause newClause = *kbCurrentNew | *(kbIterator++);

			// If the new clause is an empty one => contradiction
			if (newClause.size() == 0) {
				return true;
			}
			// if the new clause doesn't exist in the set, add it to the addition KB
			else if((processedKB.clauses.find(newClause) == processedKB.clauses.end()
				&& newKB.clauses.find(newClause) == newKB.clauses.end())){
				additionalKnowledgeBase += newClause;
			}
		}
		++kbCurrentNew;
	}

	// Nothing is added and no empty clause is found
	// meaning no contradiction => original clause doesn't follow from the axioms
	if (additionalKnowledgeBase.size() == 0) { 
		return false;
	}

	// Else, our search continues
	processedKB += newKB;

	return ResolveKB(processedKB, additionalKnowledgeBase);
}

// Note to whomever reads this
// I've been programming for almost 8 years now
// And I have NEVER given such a cool name to a function
// Today was a good day. Today I was proud.
void KnowledgeBase::PurgeAbsoluteTruths()
{
	ClauseSet::iterator current = clauses.begin();
	ClauseSet::iterator end = clauses.end();
	while (current != end) {
		ClauseSet::iterator iter = current;
		++iter;
		while (iter != end) {

		}
	}

}
////////////////////////////////////////////////////////////////////////////
std::ostream& operator<<( std::ostream& os, KnowledgeBase const& kb ) {
    unsigned size = kb.clauses.size();
    for(ClauseSet::const_iterator it1 = kb.clauses.begin(); it1 != kb.clauses.end(); ++it1) {
        os << *it1 << ", ";
    }
    return os;
}

CNF const CNF::operator~() const
{
	//if CNF is made of a single clause: A | B | ~C,
	//negating it gives ~A & ~B & C (3 clauses)
	//otherwise
	//CNF = clause1 & clause2 & clause3,
	//~CNF = ~clause1 | ~clause2 | ~clause3 
	//"or" is defined later 

	if (clauses.size() == 0)
		return CNF();

	ClauseSet::const_iterator iter = clauses.begin();
	ClauseSet::const_iterator end = clauses.end();

	CNF result = ~(*(iter++));

	while (iter != end) {
		result = result | ~(*(iter++));
	}

	return result;
}

CNF const CNF::operator&(CNF const & op2) const
{
	//CNF1 = clause1 & clause2 & clause3,
	//CNF2 = clause4 & clause5 & clause6,
	//CNF1 & CNF2 = clause1 & clause2 & clause3 & clause4 & clause5 & clause6

	// If one of the CNFs size is 0, return the other one
	if (clauses.size() == 0)
		return op2;
	else if (op2.size() == 0)
		return *this;

	// Copy CNF1 to the result
	CNF result(*this);

	// insert op2 into this
	result.clauses.insert(op2.begin(), op2.end());

	return result;
}

CNF const CNF::operator|(CNF const & op2) const
{
	//CNF1 = clause1 & clause2 & clause3,
	//CNF2 = clause4 & clause5 & clause6,
	//CNF1 | CNF2 = 
	//              c1|c4 & c1|c5 & c1|c6    &
	//              c2|c4 & c2|c5 & c2|c6    &
	//              c3|c4 & c3|c5 & c3|c6

	// If one of the CNFs size is 0, return the other one
	if (clauses.size() == 0)
		return op2;
	else if (op2.size() == 0)
		return *this;

	CNF result;

	ClauseSet::const_iterator iter1 = clauses.begin();
	ClauseSet::const_iterator end1 = clauses.end();

	ClauseSet::const_iterator iter2;
	ClauseSet::const_iterator end2 = op2.end();

	while (iter1 != end1) {
		iter2 = op2.begin();
		while (iter2 != end2) {
			result.clauses.insert(*iter1 | *(iter2++));
		}
		++iter1;
	}

	return result;

}

Clause const Clause::operator|(Clause const & op2) const
{
	// Check sizes, send the non-zero one back
	if (literals.size() == 0)
		return op2;

	if (op2.size() == 0)
		return *this;

	// copy this first
	Clause result(*this);

	result.literals.insert(op2.begin(), op2.end());

	// "Logical Housekeeping"
	// If the set contains complementary literals, remove them from the set
	// NOTE: HOW THE HELL THIS DISGUSTING BLOCK OF CODE IS FASTER THAN THE BEAUTY BELOW
	// I honestly don't get it
	LiteralSet::iterator current = result.begin();
	LiteralSet::iterator iter;
	LiteralSet::iterator end = result.end();
	bool isSomethingRemoved = false;
	while (current != end) {
		iter = current;
		++iter;
		while (iter != end) {
			if (current->Complementary(*iter)) {
				result.literals.erase(iter);
				LiteralSet::iterator literalToBeRemoved = current++;
				result.literals.erase(literalToBeRemoved);
				isSomethingRemoved = true;
				break;
			}
			else {
				++iter;
			}
		}
		if (!isSomethingRemoved) {
			++current;
		}
		else {
			isSomethingRemoved = false;
		}
		
		/*Literal literalToCheck(*current);
		literalToCheck.Negate();
		if (result.literals.erase(literalToCheck) > 0) {
			LiteralSet::iterator literalToBeRemoved = current++;
			result.literals.erase(literalToBeRemoved);
		}
		else {
			++current;
		}*/
	}

	return result;
}

ClauseSet Clause::operator~() const
{
	ClauseSet negatedLiteralSet;
	LiteralSet::const_iterator iterator = literals.begin();
	LiteralSet::const_iterator end = literals.end();
	while (iterator != end) {
		negatedLiteralSet.insert(~(*(iterator++)));
	}
	return negatedLiteralSet;
}

std::string Clause::ToString() const
{
	std::string stringForm;
	LiteralSet::const_iterator iter = literals.begin();
	LiteralSet::const_iterator end = literals.end();

	while (iter != end) {
		stringForm.append((iter++)->Name());
		stringForm.append("|");
	}
	// removing the extra OR sign
	if (stringForm.size() > 0) {
		stringForm[stringForm.size() - 1] = '\0';
	}

	return stringForm;
}
