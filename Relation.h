#ifndef RELATION_H
#define RELATION_H

#include <iostream>
#include <iomanip>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <set>
#include "Tuple.h"
#include "Scheme.h"
#include "Parser.h"

using namespace std;

class Relation {
public:
	Relation() {

	}
	void setName(string newName) {
		name = newName;
	}
	string getName() const {
		return name;
	}
	void setScheme(vector<string> attributes) {
		myScheme.clear();
		for (unsigned int i = 0; i < attributes.size(); ++i) {
			myScheme.push_back(attributes.at(i));
		}
	}
	void addTuple(Predicate newFact) {
		vector<string> params = newFact.getParameterStrings();
		string factName = newFact.getID();
		if (factName == name) {
			for (unsigned int i = 0; i < myScheme.size(); ++i) {
				myTuple.push_back(params.at(i));
			}
			tupleSet.insert(myTuple);
			myTuple.clear();
		}
	}
	void addTuple(Tuple newTuple) {
		tupleSet.insert(newTuple);
	}
	void addTuple(vector<string> newVec) {
		for (unsigned int i = 0; i < myScheme.size(); ++i) {
			myTuple.push_back(newVec.at(i));
		}
		tupleSet.insert(myTuple);
		myTuple.clear();
	}
	void clear() {
		name = "";
		myTuple.clear();
		myScheme.clear();
		tupleSet.clear();
		
	}
	Relation selectStr(string str, int index, Relation myRel) { 
		Relation newRelation;
		newRelation.setName(myRel.name);
		newRelation.setScheme(myRel.myScheme);
	
		for (iter = myRel.tupleSet.begin(); iter != myRel.tupleSet.end(); ++iter) {
			Tuple newTuple = *iter;
			if (newTuple.at(index) == str) {
				newRelation.addTuple(newTuple);
			}
		}

		return newRelation;
	}
	Relation selectCol(Relation myRel, int x, int y) {
		Relation newRelation;
		newRelation.setName(myRel.name);
		newRelation.setScheme(myRel.myScheme);

		for (iter = myRel.tupleSet.begin(); iter != myRel.tupleSet.end(); ++iter) {
			Tuple newTuple = *iter;
			if (newTuple.at(x) == newTuple.at(y)) {
				newRelation.addTuple(newTuple);
			}
		}
		return newRelation;
	}
	Relation project(vector<int> projectIndices, Relation myRel) {
		Relation newRelation;
		newRelation.setName(myRel.name);
		vector<string> newAttributes;
		set<Tuple> newTupleSet;
		for (unsigned int i = 0; i < projectIndices.size(); ++i) {
			newAttributes.push_back(myRel.myScheme.at(projectIndices.at(i)));
		}
		newRelation.setScheme(newAttributes);
		for (myRel.iter = myRel.tupleSet.begin(); myRel.iter != myRel.tupleSet.end(); ++myRel.iter) {
			Tuple newTuple = *myRel.iter; //we have a problem
			vector<string> newVec;
			for (unsigned int i = 0; i < projectIndices.size(); ++i) {
				newVec.push_back(newTuple.at(projectIndices.at(i)));
			}
			newRelation.addTuple(newVec);
		}

		return newRelation;
	}
	Relation rename(vector<string> renameVec, Relation myRel) {
		myRel.setScheme(renameVec);
		return myRel;
	}
	int getSize() const {
		return tupleSet.size();
	}
	Scheme getScheme() const {
		return myScheme;
	}
	set<Tuple> getTuples() const {
		return tupleSet;
	}

private:
	string name;
	Tuple myTuple;
	Scheme myScheme;
	set<Tuple> tupleSet;
	set<Tuple>::iterator iter;
	set<int> testSet;

};

#endif