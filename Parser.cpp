#include <iostream>
#include <iomanip>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include "Parser.h"

using namespace std;

bool Parser::match(Types typeA) {
	if (mySet.at(i).getType() == COMMENT) {
		++i;
		match(typeA);
		return true;
	}
	else if (mySet.at(i).getType() == typeA) {
		++i;
		return true;
	}
	throw i;
}

string Parser::datalogProgram() {
	string returnString = "Success!\n";

	try {
		currentType = 's';
		match(SCHEMES);
		match(COLON);
		scheme();
		schemeList();
		
		currentType = 'f';
		match(FACTS);
		match(COLON);
		factList();

		currentType = 'r';
		match(RULES);
		match(COLON);
		ruleList(); 

		currentType = 'q';
		match(QUERIES);
		match(COLON);
		query();
		queryList();
		match(END);

		returnString += "Schemes(" + to_string(schemes.size()) + "):\n";
		for (unsigned int i = 0; i < schemes.size(); ++i) {
			returnString += "  " + schemes.at(i).toString() + "\n";
		}

		returnString += "Facts(" + to_string(facts.size()) + "):\n";
		for (unsigned int i = 0; i < facts.size(); ++i) {
			returnString += "  " + facts.at(i).toString() + ".\n";
		}

		returnString += "Rules(" + to_string(rules.size()) + "):\n";
		for (unsigned int i = 0; i < rules.size(); ++i) {
			returnString += "  " + rules.at(i).toString() + "\n";
		}

		returnString += "Queries(" + to_string(queries.size()) + "):\n";
		for (unsigned int i = 0; i < queries.size(); ++i) {
			returnString += "  " + queries.at(i).toString() + "?\n";
		}

		returnString += "Domain(" + to_string(domain.size()) + "):\n";
		for (set<string>::iterator i = domain.begin(); i != domain.end(); ++i) {
			returnString += "  " + *i + "\n";
		}

	}
	catch (int error) {
		returnString = "Failure! \n " + mySet.at(error).toString() + "\n";
	}

	return returnString;
}

void Parser::addPredicate() {
	if (currentType == 's') {
		schemes.push_back(newPred);
	}
	else if (currentType == 'f') {
		facts.push_back(newPred);
	}
	else if (currentType == 'q') {
		queries.push_back(newPred);
	}
	else if (currentType == 'r') {
		rulePreds.push_back(newPred);
	}

	newPred.clear();
}

void Parser::addToRule() {
	for (unsigned int i = 0; i < rulePreds.size(); ++i) {
		newRule.addPredicate(rulePreds.at(i));
	}
	rules.push_back(newRule);
	newRule.clear();
	rulePreds.erase(rulePreds.begin(), rulePreds.end());
}

bool Parser::scheme() {
		headPredicate();
		return true;
}

bool Parser::headPredicate() {
	
		match(ID);
		newPred.setID(mySet.at(i - 1));
		match(LEFT_PAREN);
		match(ID);
		newPred.addParameter(mySet.at(i - 1));
		idList();
		match(RIGHT_PAREN);
		if (currentType == 'r') {
			newRule.addHeadPredicate(newPred);
			newPred.clear();
		}
		else {
			addPredicate();
		}
		return true;
}

bool Parser::idList() {

	try {
		match(COMMA);
		match(ID);
		newPred.addParameter(mySet.at(i - 1));
		idList();
	}
	catch (...) {
		if (mySet.at(i - 1).getType() == ID) {
			match(RIGHT_PAREN); 
			--i;
		}
		else {
			throw i;
		}
	}
	return true;
}

bool Parser::schemeList() {
	try {
		scheme();
		schemeList();
	}
	catch (...) {
		match(FACTS);
		--i;
	}
	return true;
}

bool Parser::factList() {
	try {
		if (mySet.at(i).getType() == RULES) {
			return true;
		}
		fact();
		factList();
	}
	catch (...) {
		if (mySet.at(i - 1).getType() == PERIOD) {
			match(RULES);
			--i;
		}
		else if (mySet.at(i - 1).getType() == COMMENT) {
			if (mySet.at(i - 2).getType() == PERIOD) {
				match(RULES);
				--i;
			}
		}
		else {
			throw i;
		}
		
	}
	return true;
}

bool Parser::fact() {
	match(ID);
	newPred.setID(mySet.at(i - 1));
	match(LEFT_PAREN);
	match(STRING);
	domain.insert(mySet.at(i - 1).getData());
	newPred.addParameter(mySet.at(i - 1));
	stringList();
	match(RIGHT_PAREN);
	match(PERIOD);
	addPredicate();
	return true;
}

bool Parser::stringList() {
	try {
		match(COMMA);
		match(STRING);
		if (currentType == 'f') {
			domain.insert(mySet.at(i - 1).getData());
		}
		newPred.addParameter(mySet.at(i - 1));
		stringList();
	}
	catch (...) {
		if (mySet.at(i - 1).getType() == STRING) {
			match(RIGHT_PAREN);
			--i;
		}
		else {
			throw i;
		}
	}
	return true;
}

bool Parser::rule() {
	headPredicate();
	match(COLON_DASH);
	predicate();
	predicateList();
	match(PERIOD);
	addToRule();
	return true;
}

bool Parser::ruleList() {
	try {
		if (mySet.at(i).getType() == QUERIES) {
			return true;
		}
		rule();
		ruleList();
	}
	catch (...) {
		if (mySet.at(i - 1).getType() == PERIOD) {
			match(QUERIES);
			--i;
		}
		else if (mySet.at(i - 1).getType() == COMMENT) {
			if (mySet.at(i - 2).getType() == PERIOD) {
				match(QUERIES);
				--i;
			}
		}
		else {
			throw i;
		}
		
	}
	return true;
}

bool Parser::query() {
	predicate();
	match(Q_MARK);
	return true;
}

bool Parser::queryList() {
	try {
		query();
		queryList();
	}
	catch (...) {
		match(END);
		--i;
	}
	return true;
}

bool Parser::predicate() {
	match(ID);
	newPred.setID(mySet.at(i - 1));
	match(LEFT_PAREN);
	parameter();
	if (expString.size() > 0) {
		expToken.setType(STRING);
		expToken.setData(expString);
		expToken.setLine(mySet.at(i - 1).getLine());
		newPred.addParameter(expToken);
		expString.clear();
		expToken.clear();
		
	}
	parameterList();
	match(RIGHT_PAREN);
	addPredicate();
	return true;
}

bool Parser::predicateList() {
	try {
		match(COMMA);
		predicate();
		predicateList();
	}
	catch (...) {
		match(PERIOD);
		--i;
	}
	return true;
}

bool Parser::parameterList() {
	try {
		match(COMMA);
		parameter();
		if (expString.size() > 0) {
			expToken.setType(STRING);
			expToken.setData(expString);
			expToken.setLine(mySet.at(i - 1).getLine());
			newPred.addParameter(expToken);
			expString.clear();
			expToken.clear();

		}
		parameterList();
	}
	catch (...) {
		if (isParameter(i - 1)) {
			match(RIGHT_PAREN);
			--i;
		}
		else if (mySet.at(i - 1).getType() == RIGHT_PAREN) {
			match(RIGHT_PAREN);
			--i;
		}
		else {
			throw i;
		}
	}
	return true;
}

bool Parser::isParameter(int i) {
	try {
		if (mySet.at(i).getType() == ID) {
			return true;
		}
		else if (mySet.at(i).getType() == STRING) {
			return true;
		}
		else if (expression()) {
			return true;
		}
		else {
			return false;
		}
	}
	catch(...) {
		return false;
	}
}
//IM IN THE WEEDS GENTS

bool Parser::parameter() { 
		if (mySet.at(i).getType() == ID) {
			match(ID);
			if (!isExpression) {
				newPred.addParameter(mySet.at(i - 1));
			}
		}
		else if (mySet.at(i).getType() == STRING) {
			match(STRING);
			if (!isExpression) {
				newPred.addParameter(mySet.at(i - 1));
			}
		}
		else if (isExp()) {
			expression(); 
		
			return true;
		}
		else {
			throw i;
		}

	return true;
}

bool Parser::oper() {
	
		if (mySet.at(i).getType() == ADD) {
			match(ADD); 
		}
		else if (mySet.at(i).getType() == MULTIPLY) {
			match(MULTIPLY);
		}
		else {
			throw i;
		}
	
	return true;
}

bool Parser::expression() {
	
	match(LEFT_PAREN);
	isExpression = true;
	expString += mySet.at(i - 1).getData();
	parameter(); 
	isExpression = true;
	if (mySet.at(i-1).getType() != RIGHT_PAREN) {
		expString += mySet.at(i - 1).getData();
	}
	oper();
	expString += mySet.at(i - 1).getData();
	parameter();
	isExpression = true;
	if (mySet.at(i - 1).getType() != RIGHT_PAREN) {
		expString += mySet.at(i - 1).getData(); 
	}
	match(RIGHT_PAREN);
	expString += mySet.at(i - 1).getData();

	isExpression = false;
	return true;
}

bool Parser::isExp() {
	if (mySet.at(i).getType() == LEFT_PAREN) {
		return true;
	}
	return false;
}