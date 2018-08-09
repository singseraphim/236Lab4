#include <iostream>
#include <iomanip>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include "Token.h"
#include "TokenSet.h"
#include "Tokenizer.h"

using namespace std;

string extractWord(unsigned int i, string inString) {
	unsigned int j = i;
	string word;
	while (isalnum(inString.at(j))) {
		word += inString.at(j);
		++j;
		if (j >= inString.length()) {
			break;
		}
	}
	return word;
}

bool end(unsigned int& i, unsigned int& fileIndex, ifstream& in, string& inString, unsigned int& lineNumber, Types& type) {
	if (i == inString.length() - 1) {
		return true;
	}
	if (inString.at(i + 1) != '\'') {
		return true;
	}
	return false;
}

string extractQuote(unsigned int& i, unsigned int& fileIndex, ifstream& in, string& inString, unsigned int& lineNumber, Types& type) {
	string quote;
	bool isEnd = false;
	quote += inString.at(i);
	i++;

	while (true) {
		for (; i < inString.length(); i++) {
			quote += inString.at(i);
			if (inString.at(i) == '\'') {
				if (end(i, fileIndex, in, inString, lineNumber, type)) {
					isEnd = true;
					break;
				}
				else {
					i++;
					++fileIndex;
					quote += inString.at(i);
				}
			}
			++fileIndex;
		}
		if (in.eof()) {
			if (!isEnd) {
				type = UNDEFINED;
			}
			break;
		}
		if (!isEnd) {
			getline(in, inString);
			++lineNumber;
			quote += '\n';
			i = 0;
		}
		else {
			break;
		}

	}
	return quote;
}

string extractMultiComment(unsigned int& i, unsigned int& fileIndex, ifstream& in, string& inString, unsigned int& lineNumber, Types& type) {
	string comment;
	bool isEnd = false;

	while (true) {
		for (; i < inString.length(); i++) {
			comment += inString.at(i);
			if (inString.at(i) == '|') {
				if (inString.at(i + 1) == '#') {
					++i;
					++fileIndex;
					comment += inString.at(i);
					isEnd = true;
					break;
				}
			}
			++fileIndex;
		}
		if (in.eof()) {
			if (!isEnd) {
				type = UNDEFINED;
			}
			break;
		}
		if (!isEnd) {
			getline(in, inString);
			++lineNumber;
			comment += '\n';
			i = 0;
		}
		else {
			break;
		}
	}

	return comment;
}

string extractSingleComment(unsigned int i, string inString) {
	string comment;
	for (; i < inString.length(); i++) {
		comment += inString.at(i);
	}
	return comment;
}

Types getType(string word) {

	if (word == "Schemes") {
		return SCHEMES;
	}
	else if (word == "Facts") {
		return FACTS;
	}
	else if (word == "Rules") {
		return RULES;
	}
	else if (word == "Queries") {
		return QUERIES;
	}
	else {
		return ID;
	}

}

int getIndex(unsigned int i, string word) {
	return i + word.length() - 1;
}

void setData(Token& newToken, Types type, string data, unsigned int line) {
	newToken.setType(type);
	newToken.setData(data);
	newToken.setLine(line);
	return;
}

void defaultFunctions(unsigned int& i, unsigned int& fileIndex, ifstream& in, string& inString, unsigned int& lineNumber, Types& type, string& data) {
	string word;
	if (!isalpha(inString.at(i))) {
		type = UNDEFINED;
		data = inString.at(i);
		return;
	}
	word = extractWord(i, inString);
	if (word.back() == ':') {
		word = word.substr(0, word.length() - 1);
	}
	type = getType(word);
	i = getIndex(i, word);
	fileIndex = getIndex(fileIndex, word);
	data = word;
}

void getComment(unsigned int& i, unsigned int& fileIndex, ifstream& in, string& inString, unsigned int& lineNumber, Types& type, string& data) {
	unsigned int n;
	if (i == inString.length() - 1) {
		n = ' ';
	}
	else {
		n = inString.at(i + 1);
	}
	if (n == '|') {
		data = extractMultiComment(i, fileIndex, in, inString, lineNumber, type);
	}
	else {
		data = extractSingleComment(i, inString);
		i = inString.length() - 1;
	}
}

TokenSet tokenizer(ifstream& in) {
	
	char c;
	char n;
	string inString;
	Types type;
	string data;
	string word;
	TokenSet mySet;
	Token newToken;
	bool isBlank = false;
	unsigned int line = 1;
	unsigned int lineStart = line;
	unsigned int fileIndex = 0;
	while (getline(in, inString)) {
		for (unsigned int i = 0; i < inString.length(); i++) {
			c = inString.at(i);
			switch (c) {
			case '\n':
				++line;
				break;
			case '\t':
				isBlank = true;
				break;
			case ',':
				type = COMMA;
				data = ",";
				break;
			case '.':
				type = PERIOD;
				data = ".";
				break;
			case '?':
				type = Q_MARK;
				data = "?";
				break;
			case '(':
				type = LEFT_PAREN;
				data = "(";
				break;
			case ')':
				type = RIGHT_PAREN;
				data = ")";
				break;
			case ':':
				if (i == inString.length() - 1) {
					n = ' ';
				}
				else {
					n = inString.at(i + 1);
				}
				if (n == '-') {
					type = COLON_DASH;
					data = ":-";
					++i;
					++fileIndex;
				}
				else {
					type = COLON;
					data = ":";
				}
				break;
			case '*':
				type = MULTIPLY;
				data = "*";
				break;
			case '+':
				type = ADD;
				data = "+";
				break;
			case '\'':
				type = STRING;
				data = extractQuote(i, fileIndex, in, inString, line, type);
				break;
			case ' ':
				isBlank = true;
				break;
			case '#':
				type = COMMENT;
				getComment(i, fileIndex, in, inString, line, type, data);
				break;

			default:
				defaultFunctions(i, fileIndex, in, inString, line, type, data);
			}
			if (!isBlank) {
				setData(newToken, type, data, lineStart);
				mySet.addToken(newToken);
			}
			isBlank = false;
			++fileIndex;
		}

		++line;
		lineStart = line;
	}
	setData(newToken, END, "", line);
	mySet.addToken(newToken);
	return mySet;
}



//while (getline(inputFile, currentString)) {
//	for (int i = 0; i < currentString.length(); ++i) {
//		//process currentString one character at a time
//	}
//	++line;
//}



