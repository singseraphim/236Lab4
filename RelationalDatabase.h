#ifndef RELATIONALDATABASE_H
#define RELATIONALDATABASE_H

#include <iostream>
#include <iomanip>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <set>
#include <map>
#include "Relation.h"
#include "Parser.h"

using namespace std;

class RelationalDatabase {
public:
	RelationalDatabase() {

	}
	void getData(Parser myParser);
	void evaluate();
	void setRelations();
	void addFacts();
	void doQueries();
	void evaluateRules();
	string relationString(Relation&);
	vector<Relation> doRule(Rule);
	int findMatchIndex(vector<Parameter>, int);
	Relation join(vector<Relation>&);
	Scheme joinSchemes(Scheme, Predicate);
	Scheme joinSchemes(Relation&, Relation&);
	void evaluateRule(Rule);
	bool canJoin(Relation&, Relation&, Tuple, Tuple, vector<int>&, vector<int>&);
	Relation select(Predicate, map<string, int>&, vector<int>&, vector<string>&);
	Relation joinTwoRels(Relation&, Relation&);
	Tuple combineTuples(const Relation&, const Relation&, Tuple, Tuple, Scheme, vector<int>&, vector<int>&);
	Relation project(Relation&, Scheme);
	vector<int> getHeadIndices(Relation&, Scheme);
	vector<int> getMatchIndices(Scheme, Scheme);
	bool isSameScheme(int, int, Relation&, Relation&);

private:
	vector<Predicate> facts;
	vector<Predicate> queries;
	vector<Predicate> schemes;
	vector<Relation> relationSet;
	vector<Rule> rules;
	Relation myRelation;
	map<string, Relation> relationMap;
	int currentSize;
};

#endif
