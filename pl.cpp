#include "pl.h"

CNF const operator|( Literal const& op1, Literal const& op2 ) { return CNF(op1)|CNF(op2); }
CNF const operator|( Literal const& op1, CNF     const& op2 ) { return CNF(op1)|op2; }
CNF const operator&( Literal const& op1, Literal const& op2 ) { return CNF(op1)&CNF(op2); }
CNF const operator&( Literal const& op1, CNF     const& op2 ) { return CNF(op1)&op2; }
CNF const operator>( Literal const& op1, Literal const& op2 ) { return CNF(op1)>CNF(op2); }
CNF const operator>( Literal const& op1, CNF     const& op2 ) { return CNF(op1)>op2; }


KnowledgeBase::KnowledgeBase() : clauses() {}
////////////////////////////////////////////////////////////////////////////
KnowledgeBase& KnowledgeBase::operator+=( CNF const& cnf ) {
    for ( ClauseSet::const_iterator it = cnf.begin(); it != cnf.end(); ++it ) {
        clauses.insert( *it );
    }
    return *this;
}
KnowledgeBase & KnowledgeBase::operator+=(Literal const & literal)
{
	CNF cnf = literal;
	return (*this += cnf);
}
KnowledgeBase & KnowledgeBase::operator+=(KnowledgeBase const & kb)
{
	for (ClauseSet::const_iterator it = kb.begin(); it != kb.end(); ++it) {
		clauses.insert(*it);
	}
	return *this;
}
////////////////////////////////////////////////////////////////////////
ClauseSet::const_iterator KnowledgeBase::begin() const { return clauses.begin(); }
ClauseSet::const_iterator KnowledgeBase::end()   const { return clauses.end(); }
unsigned                           KnowledgeBase::size()  const { return clauses.size(); }
////////////////////////////////////////////////////////////////////////////
bool KnowledgeBase::ProveByRefutation( CNF const& alpha ) const {

	KnowledgeBase intermediateKnowledgeBase(*this);
	intermediateKnowledgeBase += ~alpha;
	return ResolveKB(intermediateKnowledgeBase);
}
bool KnowledgeBase::ResolveKB(KnowledgeBase & KB) const
{
	// KB to be added to the original one
	KnowledgeBase additionalKnowledgeBase;
	// Get iterators to beginning and the end
	ClauseSet::const_iterator kbCurrent = KB.clauses.begin();
	ClauseSet::const_iterator kbEnd = KB.clauses.end();
	while (kbCurrent != kbEnd) {
		// kbIterator starts from kbCurrent+1 to end for the rest of clauses in KB
		ClauseSet::const_iterator kbIterator = kbCurrent;
		++kbIterator;
		while (kbIterator != kbEnd) { //go through all the other clauses
			Clause newClause = *kbCurrent | *(kbIterator++);

			// If the new clause is an empty one => contradiction
			if (newClause.size() == 0) {
				return true;
			}
			// if the new clause doesn't exist in the set, add it to the addition KB
			else if(clauses.find(newClause) == clauses.end()){ 
				additionalKnowledgeBase += newClause;
			}
			else {
				printf("WTF\n");
			}
		}
		++kbCurrent;
	}

	// Nothing is added and no empty clause is found
	// meaning no contradiction => original clause doesn't follow from the axioms
	if (additionalKnowledgeBase.size() == 0) { 
		return false;
	}

	// Else, our search continues
	KnowledgeBase newKnowledgeBase;
	newKnowledgeBase += KB;
	newKnowledgeBase += additionalKnowledgeBase;

	return ResolveKB(newKnowledgeBase);
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
	LiteralSet::iterator current = result.begin();
	LiteralSet::iterator end = result.end();
	while (current != end) {
		Literal literalToCheck(*current);
		literalToCheck.Negate();
		if (result.literals.erase(literalToCheck) > 0) {
			LiteralSet::iterator literalToBeRemoved = current++;
			result.literals.erase(literalToBeRemoved);
		}
		else {
			++current;
		}
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
