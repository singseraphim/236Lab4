#ifndef TOKEN_H
#define TOKEN_H
#include <string>
using namespace std;
enum Types { COMMA, PERIOD, Q_MARK, LEFT_PAREN, RIGHT_PAREN, COLON, COLON_DASH, MULTIPLY, ADD, SCHEMES, FACTS, RULES, QUERIES, ID, STRING, COMMENT, UNDEFINED, END, EMPTY };
class Token {
public:

	Token() {
		data = "";
		lineNum = 0;
		type = EMPTY;
	}
	string toString() {
		return "(" + typeString() + ",\"" + data + "\"," + to_string(lineNum) + ")";
	}
	void setType(Types t) {
		type = t;
		return;
	}
	void setData(string s) {
		data = s;
		return;
	}
	void setLine(int n) {
		lineNum = n;
		return;
	}
	Types getType() {
		return type;
	}
	string getData() {
		return data;
	}
	int getLine() {
		return lineNum;
	}

	void clear() {
		data = "";
		lineNum = 0;
		type = EMPTY;
	}

	string typeString() {
		switch (type) {
		case 0:
			return "COMMA";
		case 1:
			return "PERIOD";
		case 2:
			return "Q_MARK";
		case 3:
			return "LEFT_PAREN";
		case 4:
			return "RIGHT_PAREN";
		case 5:
			return "COLON";
		case 6:
			return "COLON_DASH";
		case 7:
			return "MULTIPLY";
		case 8:
			return "ADD";
		case 9:
			return "SCHEMES";
		case 10:
			return "FACTS";
		case 11:
			return "RULES";
		case 12:
			return "QUERIES";
		case 13:
			return "ID";
		case 14:
			return "STRING";
		case 15:
			return "COMMENT";
		case 16:
			return "UNDEFINED";
		case 17:
			return "EOF";
		default:
			return "ERROR";
		}
	}

private:
	Types type;
	string data;
	int lineNum;
};

#endif