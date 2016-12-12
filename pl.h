#ifndef PL4_H
#define PL4_H

#include <string>
#include <fstream>
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <algorithm>

class Literal {
    public:

        Literal( std::string const& _name ) : name(_name), negated(false) { }
        Literal( ) : name(""), negated(false) { } // just for map.operator[]
        ////////////////////////////////////////////////////////////////////////
       void Negate() { negated = !negated; }
        bool IsPositive() const { return !negated; }
        ////////////////////////////////////////////////////////////////////////
        bool operator==( Literal const& op2 ) const {
            Literal const& op1 = *this;
            return ( op1.negated == op2.negated ) && ( op1.name == op2.name );
        }
        ////////////////////////////////////////////////////////////////////////
        bool operator<( Literal const& op2 ) const {
            Literal const& op1 = *this;
            //negated infront
            if ( op1.negated && !op2.negated ) {
                return true;
            }
            if ( !op1.negated && op2.negated ) {
                return false;
            }
            return ( op1.name < op2.name );
        }

        ////////////////////////////////////////////////////////////////////////
        Literal operator~() const { 
            Literal result( *this );
            result.Negate();
            return result;
        }
        ////////////////////////////////////////////////////////////////////////
        bool Complementary( Literal const& op2 ) const {
            return ( name == op2.name ) && ( negated != op2.negated );
        }
        ////////////////////////////////////////////////////////////////////////
        friend std::ostream& operator<<( std::ostream& os, Literal const& literal ) {
            os << (literal.negated?"~":"") << literal.name;
            return os;
        }
		std::string const & Name() const { return name; }
    private:
        std::string name;
        bool negated;
};

typedef std::set<Literal> LiteralSet;

class Clause {
    public:
		Clause(LiteralSet const & literals) : literals(literals){};
		Clause(Literal const & singleLiteral) {
			literals.insert(singleLiteral);
		}

		bool operator<(Clause const& op2) const {
			return literals < op2.literals;
		}

		Clause const operator|(Clause const& op2) const;

		unsigned size() const { return literals.size(); }
		LiteralSet::const_iterator begin() const { return literals.begin(); }
		LiteralSet::const_iterator end()   const { return literals.end(); }

		std::set<Clause> operator~() const;

		std::string ToString() const;

        // ..........
        // ..........
        // ..........
        // ..........
        ////////////////////////////////////////////////////////////////////////
        friend std::ostream& operator<<( std::ostream& os, Clause const& clause ) {
            unsigned size = clause.literals.size();

            if ( clause.size() == 0 ) {
                os << " FALSE ";
            } else {
				LiteralSet::const_iterator it = clause.literals.begin();
                os << "( " << *it;
                ++it;
                for ( ; it!=clause.literals.end(); ++it ) {
                    os << " | " << *it;
                }
                os << " ) ";
            }
            return os;
        }
    private:
		LiteralSet literals;
};

typedef std::set<Clause> ClauseSet;

class CNF {
    public:
		CNF() {}
		CNF(ClauseSet const & clauses) : clauses(clauses) {}
		CNF(Clause const & singleClause) {
			clauses.insert(singleClause);
		}

		CNF(Literal const & singleLiteral) {
			clauses.insert(Clause(singleLiteral));
		}

        // ..........
        // ..........
        // ..........
        // ..........
        ////////////////////////////////////////////////////////////////////////
        // not
		CNF const operator~() const;
        ////////////////////////////////////////////////////////////////////////
        // =>
        CNF const operator>( CNF const& op2 ) const {
            CNF const& op1 = *this;
            return ~(op1)|op2;
        }
        ////////////////////////////////////////////////////////////////////////
        // and
		CNF const operator&(CNF const& op2) const;
        ///////////////////////////////////////////////////////////////////////
        // or
		CNF const operator|(CNF const& op2) const;

        /////////////////////////////////////////////////////////////////////////////////
        CNF const operator>( Literal const& op2 ) const { return operator>( CNF(op2) ); }
        CNF const operator&( Literal const& op2 ) const { return operator&( CNF(op2) ); }
        CNF const operator|( Literal const& op2 ) const { return operator|( CNF(op2) ); }

        ////////////////////////////////////////////////////////////////////////
        bool Empty() const { return clauses.size()==0; }
        ////////////////////////////////////////////////////////////////////////
		ClauseSet::const_iterator begin() const { return clauses.begin(); }
		ClauseSet::const_iterator end()   const { return clauses.end(); }
        unsigned                            size()  const { return clauses.size(); }
        ////////////////////////////////////////////////////////////////////////
        friend std::ostream& operator<<( std::ostream& os, CNF const& cnf ) {
            unsigned size = cnf.clauses.size();
            for(ClauseSet::const_iterator it1 = cnf.clauses.begin(); it1 != cnf.clauses.end(); ++it1) {
                os << *it1 << ", ";
            }
            return os;
        }
    private:
		ClauseSet clauses;
};

CNF const operator|( Literal const& op1, Literal const& op2 );
CNF const operator|( Literal const& op1, CNF     const& op2 );
CNF const operator&( Literal const& op1, Literal const& op2 );
CNF const operator&( Literal const& op1, CNF     const& op2 );
CNF const operator>( Literal const& op1, Literal const& op2 );
CNF const operator>( Literal const& op1, CNF     const& op2 );

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
class KnowledgeBase {
    public:
        ////////////////////////////////////////////////////////////////////////////
        KnowledgeBase();
        ////////////////////////////////////////////////////////////////////////////
        KnowledgeBase& operator+=( CNF const& cnf );
		KnowledgeBase& operator+=(Literal const& literal);
		KnowledgeBase& operator+=(KnowledgeBase const& kb);
		KnowledgeBase& operator+=(Clause const& clause);

        ////////////////////////////////////////////////////////////////////////
		ClauseSet::const_iterator begin() const;
		ClauseSet::const_iterator end()   const;
        unsigned                           size()  const;
        ////////////////////////////////////////////////////////////////////////////
        bool ProveByRefutation( CNF const& alpha ) const;
        ////////////////////////////////////////////////////////////////////////////
        friend std::ostream& operator<<( std::ostream& os, KnowledgeBase const& kb );
    private:
		ClauseSet clauses;

		bool ResolveKB(KnowledgeBase & processedKB, KnowledgeBase & newKB) const;
		void PurgeAbsoluteTruths();
};

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
#endif
