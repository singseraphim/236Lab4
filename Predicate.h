#ifndef PREDICATE_H
#define PREDICATE_H

#include <iostream>
#include <iomanip>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include "Parser.h"
#include "Parameter.h"

using namespace std;
class Predicate {
public:
	string toString() {
		string returnString = ID + "(" + parameterList.at(0).toString();
		for (unsigned int i = 1; i < parameterList.size(); ++i) {
			returnString += "," + parameterList.at(i).toString();
		}
		returnString += ")";
		return returnString;
	}
	void setID(Token newToken) {
		ID = newToken.getData();
	}
	void setID(string newName) {
		ID = newName;
	}
	void addParameter(Token newParameter) {
		Parameter myParameter(newParameter);
		parameterList.push_back(myParameter);
	}
	void addParameter(string newParameter) {
		Parameter newParam;
		newParam.setParameter(newParameter);
		parameterList.push_back(newParam);
	}
	void clear() {
		ID = "";
		parameterList.erase(parameterList.begin(), parameterList.end());

	}
	vector<string> getParameterStrings() {
		vector<string> paramStrings;
		for (unsigned int i = 0; i < parameterList.size(); ++i) {
			paramStrings.push_back(parameterList.at(i).toString());
		}
		return paramStrings;
	}

	vector<Parameter> getParameters() {
		return parameterList;
	}

	string getID() {
		return ID;
	}
	

private:
	string ID;
	vector<Parameter> parameterList;
	


};

#endif