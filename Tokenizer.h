#ifndef TOKENIZER_H
#define TOKENIZER_H

#include <iostream>
#include <iomanip>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include "Token.h"
#include "TokenSet.h"

using namespace std;

string extractWord(unsigned int i, string inString);
bool end(unsigned int& i, unsigned int& fileIndex, ifstream& in, string& inString, unsigned int& lineNumber, Types& type);
string extractQuote(unsigned int& i, unsigned int& fileIndex, ifstream& in, string& inString, unsigned int& lineNumber, Types& type);
string extractMultiComment(unsigned int& i, unsigned int& fileIndex, ifstream& in, string& inString, unsigned int& lineNumber, Types& type);
string extractSingleComment(unsigned int i, string inString);
Types getType(string word);
int getIndex(unsigned int i, string word);
void setData(Token& newToken, Types type, string data, unsigned int line);
void defaultFunctions(unsigned int& i, unsigned int& fileIndex, ifstream& in, string& inString, unsigned int& lineNumber, Types& type, string& data);
void getComment(unsigned int& i, unsigned int& fileIndex, ifstream& in, string& inString, unsigned int& lineNumber, Types& type, string& data);
TokenSet tokenizer(ifstream& in);


#endif

