#ifndef PARAMETER_H
#define PARAMETER_H
#include <iostream>
#include <iomanip>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include "Parser.h"

using namespace std;
class Parameter {
public:
	Parameter() {
		data = "";
	}
	Parameter(Token newToken) {
		data = newToken.getData();
		type = newToken.getType();
	}
	string toString() {
		return data;
	}
	void setParameter(Token newToken) {
		data = newToken.getData();
	}
	void setParameter(string newString) {
		data = newString;
		type = STRING;
	}
	Types getType() {
		return type;
	}
private:
	string data;
	Types type;


};
#endif