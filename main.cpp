#include <iostream>
#include <iomanip>
#include <string>
#include <fstream>
#include <sstream>
#include <algorithm>
#include "Tokenizer.h"
#include "Parser.h"
#include "RelationalDatabase.h"

#ifdef _MSC_VER
#define _CRTDBG_MAP_ALLOC  
#include <crtdbg.h>
#define VS_MEM_CHECK _CrtSetDbgFlag(_CRTDBG_ALLOC_MEM_DF | _CRTDBG_LEAK_CHECK_DF);
#else
#define VS_MEM_CHECK
#endif


using namespace std;

int main(int argc, char *argv[]) {
	VS_MEM_CHECK

	ifstream in;

	in.open(argv[1]);
	if (!in.is_open()) {
		cout << "Could not open input file" << endl;
		return 0;
	}

	TokenSet mySet = tokenizer(in);
	Parser myParser;
	RelationalDatabase myDatabase;

	myParser.addSet(mySet);
	myParser.datalogProgram();

	myDatabase.getData(myParser);
	myDatabase.evaluate();
	return 0;
}