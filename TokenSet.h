#ifndef TOKENSET_H
#define TOKENSET_H
#include <string>
#include <vector>
#include "Token.h"
using namespace std;

class TokenSet {
public:
	TokenSet() {

	}
	string toString() {
		string s;
		for (unsigned int i = 0; i < set.size(); ++i) {
			s += set.at(i).toString() + '\n';
		}
		return s;
	}
	int getSize() {
		return set.size();
	}
	void addToken(Token t) {
		set.push_back(t);
		return;
	}
	Token at(int i) {
		return set.at(i);
	}

private:
	vector<Token> set;



};

#endif
