#ifndef PARSER_H
#define PARSER_H

#include <iostream>
#include <iomanip>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <set>
#include "Tokenizer.h"
#include "Parameter.h"
#include "Predicate.h"
#include "Rule.h"
using namespace std;

class Parser {
public:
	bool match(Types typeA);
	string datalogProgram();
	bool scheme();
	bool headPredicate();
	bool idList();
	bool schemeList();
	bool fact();
	bool factList();
	bool rule();
	bool ruleList();
	bool query();
	bool queryList();
	bool stringList();
	bool predicate();
	bool predicateList();
	bool parameter();
	bool parameterList();
	bool oper();
	bool expression();
	bool isParameter(int i);
	void addPredicate();
	void addToRule();
	bool isExp();
	vector<Predicate> getSchemes() {
		return schemes;
	}
	vector<Predicate>getFacts() {
		return facts;
	}
	vector<Predicate>getQueries() {
		return queries;
	}
	vector<Rule>getRules() {
		return rules;
	}

	void addSet(TokenSet set) {
		mySet = set;
	}
private:
	int i = 0;
	TokenSet mySet;
	Predicate newPred;
	Rule newRule;
	vector<Predicate> schemes;
	vector<Predicate> facts;
	vector<Predicate> queries;
	vector<Predicate> rulePreds;
	vector<Rule> rules;
	set<string> domain;
	char currentType;
	Token expToken;
	string expString;
	bool isExpression = false;
};

#endif