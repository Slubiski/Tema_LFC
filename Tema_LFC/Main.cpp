// Tema 1 LFC - Construirea unui AFD pentru o expresie regulata
// Operatori: '|' (reuniune), '*' (stelare), concatenarea (implicita, sau '.'), paranteze.
// Cuvantul vid este reprezentat prin caracterul LAMBDA (implicit '@').
// Compilare: g++ -std=c++17 -O2 -o tema1 tema1.cpp
// Rulare:    ./tema1 [fisier_intrare] [fisier_iesire]

#include <algorithm>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;

const char LAMBDA = '@';


bool IsOperator(char c) { return c == '|' || c == '*' || c == '.'; }
bool IsSymbol(char c) { return !IsOperator(c) && c != '(' && c != ')'; }  
int Prec(char c) { return c == '.' ? 2 : 1; }                             

class DeterministicFiniteAutomaton {
public:
    set<int> states;                 // Q
    set<char> alphabet;              // Sigma
    map<pair<int, char>, int> delta; // functia de tranzitie
    int initialState = 0;            // q0
    set<int> finalStates;            // F

    // starea initiala in Q, F inclus in Q, delta foloseste doar simboluri din Sigma si stari din Q
    bool VerifyAutomaton() const {
        if (!states.count(initialState)) return false;
        for (int f : finalStates)
            if (!states.count(f)) return false;
        for (const auto& [key, to] : delta) {
            if (!states.count(key.first) || !states.count(to)) return false;
            if (!alphabet.count(key.second)) return false;
        }
        return true;
    }

    void PrintAutomaton(ostream& out) const {
        out << "Stare initiala: q" << initialState << "\nStari finale: {";
        bool first = true;
        for (int f : finalStates) { out << (first ? "" : ", ") << "q" << f; first = false; }
        out << "}\n\n";
        out << "      |";
        for (char c : alphabet) out << " " << c << "\t|";
        out << "\n";
        for (int s : states) {
            out << (s == initialState ? "->" : "  ") << (finalStates.count(s) ? "*" : " ");
            out << "q" << s << "\t|";
            for (char c : alphabet) {
                auto it = delta.find({ s, c });
                if (it != delta.end()) out << " q" << it->second << "\t|";
                else out << " -\t|";
            }
            out << "\n";
        }
    }

    // word == "" reprezinta cuvantul vid
    bool CheckWord(const string& word) const {
        int cur = initialState;
        for (char c : word) {
            auto it = delta.find({ cur, c });
            if (it == delta.end()) return false;
            cur = it->second;
        }
        return finalStates.count(cur) > 0;
    }
};
using DFA = DeterministicFiniteAutomaton;

// ------------------------------------------------------------------ arbore sintactic
struct Node;
using NodePtr = shared_ptr<Node>;
struct Node {
    char val;
    NodePtr left, right;
    Node(char v, NodePtr l = nullptr, NodePtr r = nullptr) : val(v), left(l), right(r) {}
};

bool IsLambdaLeaf(const NodePtr& n) { return n->val == LAMBDA && !n->left && !n->right; }
bool IsStar(const NodePtr& n) { return n->val == '*'; }

bool SameTree(const NodePtr& a, const NodePtr& b) {
    if (!a || !b) return !a && !b;
    return a->val == b->val && SameTree(a->left, b->left) && SameTree(a->right, b->right);
}

// ------------------------------------------------------------------ (a) regex -> postfix
string RegexToPostfix(const string& r) {
    // 1. inserarea explicita a concatenarii
    string t;
    for (char c : r) {
        if (isspace(static_cast<unsigned char>(c))) continue;
        if (!t.empty()) {
            char p = t.back();
            bool endsOperand = (IsSymbol(p) || p == ')' || p == '*');
            bool startsOperand = (IsSymbol(c) || c == '(');
            if (endsOperand && startsOperand) t += '.';
        }
        t += c;
    }
    // 2. algoritmul shunting-yard ('*' este operator unar postfixat, de prioritate maxima)
    string out;
    stack<char> st;
    for (char c : t) {
        if (IsSymbol(c) || c == '*') out += c;
        else if (c == '(') st.push(c);
        else if (c == ')') {
            while (!st.empty() && st.top() != '(') { out += st.top(); st.pop(); }
            if (st.empty()) throw runtime_error("Paranteze neechilibrate");
            st.pop();
        }
        else {
            while (!st.empty() && st.top() != '(' && Prec(st.top()) >= Prec(c)) {
                out += st.top(); st.pop();
            }
            st.push(c);
        }
    }
    while (!st.empty()) {
        if (st.top() == '(') throw runtime_error("Paranteze neechilibrate");
        out += st.top(); st.pop();
    }
    return out;
}

// ------------------------------------------------------------------ (b) postfix -> arbore
NodePtr PostfixToSyntaxTree(const string& postfix) {
    stack<NodePtr> st;
    for (char c : postfix) {
        if (IsSymbol(c)) st.push(make_shared<Node>(c));
        else if (c == '*') {
            if (st.empty()) throw runtime_error("Expresie invalida");
            NodePtr a = st.top(); st.pop();
            st.push(make_shared<Node>('*', a));
        }
        else {
            if (st.size() < 2) throw runtime_error("Expresie invalida");
            NodePtr b = st.top(); st.pop();
            NodePtr a = st.top(); st.pop();
            st.push(make_shared<Node>(c, a, b));
        }
    }
    if (st.size() != 1) throw runtime_error("Expresie invalida");
    return st.top();
}

// ------------------------------------------------------------------ (c) simplificare (bottom-up, arbore nou)
NodePtr SimplifySyntaxTree(const NodePtr& n) {
    if (!n) return nullptr;
    if (!n->left && !n->right) return make_shared<Node>(n->val);

    if (n->val == '*') {
        NodePtr c = SimplifySyntaxTree(n->left);
        if (IsLambdaLeaf(c)) return c;          // lambda* = lambda
        if (IsStar(c)) return c;                // (r*)* = r*
        if (c->val == '|') {                    // (lambda | r)* = (r | lambda)* = r*
            NodePtr other = nullptr;
            if (IsLambdaLeaf(c->left)) other = c->right;
            else if (IsLambdaLeaf(c->right)) other = c->left;
            if (other) return IsStar(other) ? other : make_shared<Node>('*', other);
        }
        return make_shared<Node>('*', c);
    }

    NodePtr a = SimplifySyntaxTree(n->left);
    NodePtr b = SimplifySyntaxTree(n->right);

    if (n->val == '.') {
        if (IsLambdaLeaf(a)) return b;                     // lambda . r = r
        if (IsLambdaLeaf(b)) return a;                     // r . lambda = r
        if (IsStar(a) && IsStar(b) && SameTree(a, b)) return a;  // r* . r* = r*
        return make_shared<Node>('.', a, b);
    }

    // reuniune
    if (SameTree(a, b)) return a;                                   // r | r = r
    if (IsLambdaLeaf(a) && IsStar(b)) return b;                     // lambda | r* = r*
    if (IsLambdaLeaf(b) && IsStar(a)) return a;
    if (IsStar(a) && SameTree(a->left, b)) return a;               // r* | r = r*
    if (IsStar(b) && SameTree(b->left, a)) return b;
    return make_shared<Node>('|', a, b);
}

// ------------------------------------------------------------------ (d) arbore -> postfix (postordine)
string SyntaxTreeToPostfix(const NodePtr& n) {
    if (!n) return "";
    return SyntaxTreeToPostfix(n->left) + SyntaxTreeToPostfix(n->right) + n->val;
}

// ------------------------------------------------------------------ parcurgeri / afisare arbore
string Preorder(const NodePtr& n) {
    if (!n) return "";
    return string(1, n->val) + Preorder(n->left) + Preorder(n->right);
}
string Inorder(const NodePtr& n) {  // subexpresiile binare sunt parantezate pentru a evita ambiguitatea
    if (!n) return "";
    if (!n->left && !n->right) return string(1, n->val);
    if (n->val == '*') return Inorder(n->left) + "*";
    return "(" + Inorder(n->left) + n->val + Inorder(n->right) + ")";
}
string Postorder(const NodePtr& n) { return SyntaxTreeToPostfix(n); }
void PrintLevels(const NodePtr& root, ostream& out) {
    queue<NodePtr> q;
    if (root) q.push(root);
    int level = 0;
    while (!q.empty()) {
        int sz = q.size();
        out << "  Nivel " << level++ << ": ";
        while (sz--) {
            NodePtr n = q.front(); q.pop();
            out << n->val << ' ';
            if (n->left) q.push(n->left);
            if (n->right) q.push(n->right);
        }
        out << "\n";
    }
}
void PrintTree(const string& name, const NodePtr& t) {
    cout << "Arborele " << name << ":\n";
    PrintLevels(t, cout);
    cout << "  Preordine : " << Preorder(t) << "\n";
    cout << "  Inordine  : " << Inorder(t) << "\n";
    cout << "  Postordine: " << Postorder(t) << "\n\n";
}

// ------------------------------------------------------------------ (e) postfix -> lambda-NFA (Thompson)
struct LambdaNFA {
    int numStates = 0;
    set<char> alphabet;                 // fara LAMBDA
    map<pair<int, char>, set<int>> delta;  // tranzitiile pe LAMBDA folosesc cheia LAMBDA
    int start = 0, final = 0;
    int NewState() { return numStates++; }
    void Add(int from, char c, int to) { delta[{from, c}].insert(to); }
};

LambdaNFA PostfixToLambdaNFA(const string& postfix) {
    LambdaNFA nfa;
    struct Frag { int s, f; };
    stack<Frag> st;
    for (char c : postfix) {
        if (IsSymbol(c)) {
            int s = nfa.NewState(), f = nfa.NewState();
            nfa.Add(s, c, f);  // pentru LAMBDA devine o tranzitie lambda
            if (c != LAMBDA) nfa.alphabet.insert(c);
            st.push({ s, f });
        }
        else if (c == '*') {
            if (st.empty()) throw runtime_error("Postfix invalid");
            Frag a = st.top(); st.pop();
            int s = nfa.NewState(), f = nfa.NewState();
            nfa.Add(s, LAMBDA, a.s);
            nfa.Add(s, LAMBDA, f);
            nfa.Add(a.f, LAMBDA, a.s);
            nfa.Add(a.f, LAMBDA, f);
            st.push({ s, f });
        }
        else if (c == '.') {
            if (st.size() < 2) throw runtime_error("Postfix invalid");
            Frag b = st.top(); st.pop();
            Frag a = st.top(); st.pop();
            nfa.Add(a.f, LAMBDA, b.s);
            st.push({ a.s, b.f });
        }
        else {  // '|'
            if (st.size() < 2) throw runtime_error("Postfix invalid");
            Frag b = st.top(); st.pop();
            Frag a = st.top(); st.pop();
            int s = nfa.NewState(), f = nfa.NewState();
            nfa.Add(s, LAMBDA, a.s);
            nfa.Add(s, LAMBDA, b.s);
            nfa.Add(a.f, LAMBDA, f);
            nfa.Add(b.f, LAMBDA, f);
            st.push({ s, f });
        }
    }
    if (st.size() != 1) throw runtime_error("Postfix invalid");
    nfa.start = st.top().s;
    nfa.final = st.top().f;
    return nfa;
}

// ------------------------------------------------------------------ (f) lambda-NFA -> AFD (constructia submultimilor)
set<int> LambdaClosure(const LambdaNFA& nfa, const set<int>& init) {
    set<int> res = init;
    stack<int> st;
    for (int s : init) st.push(s);
    while (!st.empty()) {
        int s = st.top(); st.pop();
        auto it = nfa.delta.find({ s, LAMBDA });
        if (it == nfa.delta.end()) continue;
        for (int t : it->second)
            if (res.insert(t).second) st.push(t);
    }
    return res;
}

DFA LambdaNFAToDFA(const LambdaNFA& nfa) {
    DFA dfa;
    dfa.alphabet = nfa.alphabet;
    map<set<int>, int> id;
    vector<set<int>> sets;
    auto getId = [&](const set<int>& s) {
        auto it = id.find(s);
        if (it != id.end()) return it->second;
        int k = sets.size();
        id[s] = k;
        sets.push_back(s);
        return k;
        };
    dfa.initialState = getId(LambdaClosure(nfa, { nfa.start }));
    for (size_t i = 0; i < sets.size(); i++) {
        set<int> cur = sets[i];
        for (char c : nfa.alphabet) {
            set<int> mv;
            for (int s : cur) {
                auto it = nfa.delta.find({ s, c });
                if (it != nfa.delta.end()) mv.insert(it->second.begin(), it->second.end());
            }
            // multimea vida devine starea "sink" (cu tranzitii in ea insasi)
            int to = getId(LambdaClosure(nfa, mv));
            dfa.delta[{(int)i, c}] = to;
        }
    }
    for (size_t i = 0; i < sets.size(); i++) {
        dfa.states.insert(i);
        if (sets[i].count(nfa.final)) dfa.finalStates.insert(i);
    }
    return dfa;
}

// ------------------------------------------------------------------ regex -> AFD
DFA RegexToDFA(const string& r, bool simplify) {
    string fp = RegexToPostfix(r);
    if (simplify) {
        NodePtr tree = PostfixToSyntaxTree(fp);
        NodePtr simp = SimplifySyntaxTree(tree);
        fp = SyntaxTreeToPostfix(simp);
    }
    LambdaNFA nfa = PostfixToLambdaNFA(fp);
    return LambdaNFAToDFA(nfa);
}

// ------------------------------------------------------------------ main
int main() {
    string inFile = "regex.txt";
    string outFile = "automat.txt";

    ifstream fin(inFile);
    if (!fin) { cerr << "Nu pot deschide fisierul " << inFile << "\n"; return 1; }
    string r;
    getline(fin, r);
    fin.close();
    cout << "Expresia regulata citita: " << r << "\n";
    cout << "(cuvantul vid este reprezentat prin '" << LAMBDA << "')\n";

    unique_ptr<DFA> dfa;
    while (true) {
        cout << "\n===== MENIU =====\n"
            << "1. Afisare forme poloneze postfixate fp(r) si fp(rs)\n"
            << "2. Afisare arbori sintactici A(r) si A(rs)\n"
            << "3. Construire AFD (RegexToDFA), validare si afisare\n"
            << "4. Verificare cuvinte in automat\n"
            << "0. Iesire\n> ";
        int opt;
        if (!(cin >> opt)) break;
        cin.ignore(numeric_limits<streamsize>::max(), '\n');
        try {
            if (opt == 0) break;
            else if (opt == 1) {
                string fp = RegexToPostfix(r);
                NodePtr simp = SimplifySyntaxTree(PostfixToSyntaxTree(fp));
                cout << "fp(r)  = " << fp << "\n";
                cout << "fp(rs) = " << SyntaxTreeToPostfix(simp) << "\n";
            }
            else if (opt == 2) {
                NodePtr t = PostfixToSyntaxTree(RegexToPostfix(r));
                NodePtr s = SimplifySyntaxTree(t);
                PrintTree("A(r)", t);
                PrintTree("A(rs)", s);
            }
            else if (opt == 3) {
                cout << "Folosesti expresia simplificata? (1 = da, 0 = nu): ";
                int sv; cin >> sv;
                cin.ignore(numeric_limits<streamsize>::max(), '\n');
                dfa = make_unique<DFA>(RegexToDFA(r, sv != 0));
                if (dfa->VerifyAutomaton()) cout << "Automatul este VALID.\n\n";
                else { cout << "Automatul este INVALID!\n"; dfa.reset(); continue; }
                dfa->PrintAutomaton(cout);
                ofstream fout(outFile);
                dfa->PrintAutomaton(fout);
                cout << "\nAutomatul a fost scris si in fisierul " << outFile << "\n";
            }
            else if (opt == 4) {
                if (!dfa) { cout << "Construieste mai intai automatul (optiunea 3).\n"; continue; }
                cout << "Introdu cuvinte (cate unul pe linie; '" << LAMBDA
                    << "' = cuvantul vid; linie goala = stop):\n";
                string w;
                while (getline(cin, w) && !w.empty()) {
                    string word = (w == string(1, LAMBDA)) ? "" : w;
                    cout << "  " << w << " -> " << (dfa->CheckWord(word) ? "ACCEPTAT" : "RESPINS") << "\n";
                }
            }
            else cout << "Optiune invalida.\n";
        }
        catch (const exception& e) {
            cout << "Eroare: " << e.what() << "\n";
        }
    }
    return 0;
}