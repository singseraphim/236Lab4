#ifndef RULE_H
#define RULE_H

#include <iostream>
#include <iomanip>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include "Parser.h"

using namespace std;
class Rule {
public:
	string toString() {
		string returnString = headPredicate.toString() + " :- " + predicateList.at(0).toString();
		for (unsigned int i = 1; i < predicateList.size(); ++i) {
			returnString += "," + predicateList.at(i).toString();
		}
		returnString += ".";
		return returnString;
	}
	void addHeadPredicate(Predicate newHeadPred) {
		headPredicate = newHeadPred;
	}
	void addPredicate(Predicate newPred) {
		predicateList.push_back(newPred);
	}
	void clear() {
		predicateList.erase(predicateList.begin(), predicateList.end());
		headPredicate.clear();
	}
	vector<Predicate> getPredicateList() {
		return predicateList;
	}
	Predicate getHeadPredicate() {
		return headPredicate;
	}

private:
	Predicate headPredicate;
	vector<Predicate> predicateList;

};

#endif