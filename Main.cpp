#include <iostream>
#include <sstream>
#include <regex>
#include <vector>
#include <pthread.h>
#include <unistd.h>
#include <time.h>
#include <errno.h>
#include <math.h>

// Minisat requirements
#include <memory>
#include "minisat/core/SolverTypes.h"
#include "minisat/core/Solver.h"

//error handlers for getcpuclockid()
#define handle_error(msg)   \
    do                      \
    {                       \
        perror(msg);        \
        exit(EXIT_FAILURE); \
    } while (0)

#define handle_error_en(en, msg) \
    do                           \
    {                            \
        errno = en;              \
        perror(msg);             \
        exit(EXIT_FAILURE);      \
    } while (0)

using namespace std;

// ------------------------ Storage Class Structures ------------------------ //

// Node Class
class Node
{
private:
    int id;
    vector<Node *> nodes;

public:
    Node(int _id)
    {
        this->id = _id;
    }

    int get_id()
    {
        return this->id;
    }

    vector<Node *> get_nodes()
    {
        return this->nodes;
    }

    void connect(Node *n)
    {
        this->nodes.push_back(n);
    }

    void disconnect(Node *other)
    {
        for (unsigned int i = 0; i < this->nodes.size(); i++)
        {
            if (this->nodes[i]->id == other->id)
            {
                this->nodes.erase(this->nodes.begin() + i);
                break;
            }
        }
    }

    bool isConnected(Node *n)
    {
        for (Node *item : this->nodes)
        {
            if (item->id == n->id)
                return true;
        }
        return false;
    }

    int degree()
    {
        return this->nodes.size();
    }
};

// Graph Class
class Graph
{
private:
    vector<Node *> nodes;

public:
    vector<Node *> get_nodes()
    {
        return this->nodes;
    }

    void fill(int number)
    {
        for (int id = 0; id < number; id++)
            nodes.push_back(new Node(id));
    }

    void clear()
    {
        for (Node *item : nodes)
        {
            delete item;
        }
        nodes.clear();
    }

    Node *findNode(int id)
    {
        for (Node *item : nodes)
        {
            if (item->get_id() == id)
                return item;
        }
        return NULL;
    }

    void ConnectNodes(Node *n1, Node *n2)
    {
        if (!n1->isConnected(n2))
            n1->connect(n2);
        if (!n2->isConnected(n1))
            n2->connect(n1);
    }

    void DisconnectNodes(Node *n1, Node *n2)
    {
        if (n1->isConnected(n2))
            n1->disconnect(n2);
        if (n2->isConnected(n1))
            n2->disconnect(n1);
    }

    int degree()
    {
        int graph_degree = 0;
        for (Node *item : this->nodes)
        {
            int temp_degree = item->degree();
            if (graph_degree < temp_degree)
                graph_degree = temp_degree;
        }
        return graph_degree;
    }

    Node *degreeNode()
    {
        int graph_degree = 0;
        Node *result;
        for (Node *item : this->nodes)
        {
            int temp_degree = item->degree();
            if (graph_degree < temp_degree)
            {
                graph_degree = temp_degree;
                result = item;
            }
        }
        return result;
    }
};

// Parser
vector<string> parser(string input)
{
    vector<string> parsedInput;
    std::string s(input);
    std::smatch m;
    std::regex e("<[0-9]+,[0-9]+>");

    while (std::regex_search(s, m, e))
    {
        for (auto x : m)
            parsedInput.push_back(x);
        s = m.suffix().str();
    }
    return parsedInput;
}

// SingleCalcDetail
class SingleCalcDetail
{
private:
    long double ratio;
    long double runtime;

public:
    SingleCalcDetail(long double runtime)
    {
        this->ratio = -1;
        this->runtime = runtime;
    }
    SingleCalcDetail(long double ratio, long double runtime)
    {
        this->ratio = ratio;
        this->runtime = runtime;
    }
    long double get_ratio()
    {
        return this->ratio;
    }
    long double get_runtime()
    {
        return this->runtime;
    }
};

// CalcData
class CalcData
{
public:
    int count_ratio, count_runtime;
    long double avg_ratio, avg_runtime, deviation_ratio, deviation_runtime;
    string Ratio_toString()
    {
        string output = "";
        output += "\tCount Ratio: " + to_string(this->count_ratio) + "\n";
        output += "\t\tAvg Ratio: " + to_string(this->avg_ratio) + "\n";
        output += "\t\tDeviation Ratio: " + to_string(this->deviation_ratio) + "\n";
        return output;
    }
    string Runtime_toString()
    {
        string output = "";
        output += "\tCount Runtime: " + to_string(this->count_runtime) + "\n";
        output += "\t\tAvg Runtime: " + to_string(this->avg_runtime) + "\n";
        output += "\t\tDeviation Runtime: " + to_string(this->deviation_runtime) + "\n";
        return output;
    }
};

// CalcStorage
class CalcStorage
{
private:
    vector<SingleCalcDetail *> CNF_SAT;
    vector<SingleCalcDetail *> APPROX_1;
    vector<SingleCalcDetail *> APPROX_2;
    CalcData *data_CNF = new CalcData();
    CalcData *data_APPROX_1 = new CalcData();
    CalcData *data_APPROX_2 = new CalcData();

public:
    int vCount;
    CalcStorage(int vCount)
    {
        this->vCount = vCount;
    }

    void add_cnf(SingleCalcDetail *item)
    {
        this->CNF_SAT.push_back(item);
    }
    void add_app1(SingleCalcDetail *item)
    {
        this->APPROX_1.push_back(item);
    }
    void add_app2(SingleCalcDetail *item)
    {
        this->APPROX_2.push_back(item);
    }
    void calc()
    {
        long double total_sum, count, temp;
        //CNF_SAT
        this->data_CNF->count_ratio = (long double)this->CNF_SAT.size();
        this->data_CNF->count_runtime = (long double)this->CNF_SAT.size();
        if (this->CNF_SAT.size() > 0)
        {
            //ratio
            this->data_CNF->avg_ratio = 1;
            this->data_CNF->deviation_ratio = 0;

            //runtime
            total_sum = 0;
            for (SingleCalcDetail *item : this->CNF_SAT)
                total_sum += item->get_runtime();
            this->data_CNF->avg_runtime = total_sum / this->data_CNF->count_runtime;

            total_sum = 0;
            for (SingleCalcDetail *item : this->CNF_SAT)
                total_sum += pow(item->get_runtime() - this->data_CNF->avg_runtime, 2);
            this->data_CNF->deviation_runtime = sqrtl(total_sum / this->data_CNF->count_runtime);
        }
        else
        {
            this->data_CNF->avg_ratio = -1;
            this->data_CNF->deviation_ratio = -1;
            this->data_CNF->avg_runtime = -1;
            this->data_CNF->deviation_runtime = -1;
        }

        //APPROX_1
        if (this->APPROX_1.size() > 0)
        {
            //ratio
            total_sum = 0;
            count = 0;
            for (SingleCalcDetail *item : this->APPROX_1)
            {
                temp = item->get_ratio();
                if (temp != -1)
                {
                    count++;
                    total_sum += temp;
                }
            }
            this->data_APPROX_1->count_ratio = count;
            if (count > 0)
                this->data_APPROX_1->avg_ratio = total_sum / count;
            else
                this->data_APPROX_1->avg_ratio = -1;

            total_sum = 0;
            for (SingleCalcDetail *item : this->APPROX_1)
            {
                temp = item->get_ratio();
                if (temp != -1)
                    total_sum += pow(temp - this->data_APPROX_1->avg_ratio, 2);
            }
            if (count > 0)
                this->data_APPROX_1->deviation_ratio = sqrtl(total_sum / count);
            else
                this->data_APPROX_1->deviation_ratio = -1;

            //runtime
            total_sum = 0;
            this->data_APPROX_1->count_runtime = (long double)this->APPROX_1.size();
            for (SingleCalcDetail *item : this->APPROX_1)
                total_sum += item->get_runtime();
            this->data_APPROX_1->avg_runtime = total_sum / this->data_APPROX_1->count_runtime;

            total_sum = 0;
            for (SingleCalcDetail *item : this->APPROX_1)
                total_sum += pow(item->get_runtime() - this->data_APPROX_1->avg_runtime, 2);
            this->data_APPROX_1->deviation_runtime = sqrtl(total_sum / this->data_APPROX_1->count_runtime);
        }
        else
        {
            this->data_APPROX_1->avg_ratio = -1;
            this->data_APPROX_1->deviation_ratio = -1;
            this->data_APPROX_1->avg_runtime = -1;
            this->data_APPROX_1->deviation_runtime = -1;
        }

        //APPROX_2
        if (this->APPROX_2.size() > 0)
        {
            //ratio
            total_sum = 0;
            count = 0;
            for (SingleCalcDetail *item : this->APPROX_2)
            {
                temp = item->get_ratio();
                if (temp != -1)
                {
                    count++;
                    total_sum += temp;
                }
            }
            this->data_APPROX_2->count_ratio = count;
            if (count > 0)
                this->data_APPROX_2->avg_ratio = total_sum / count;
            else
                this->data_APPROX_2->avg_ratio = -1;

            total_sum = 0;
            for (SingleCalcDetail *item : this->APPROX_2)
            {
                temp = item->get_ratio();
                if (temp != -1)
                    total_sum += pow(temp - this->data_APPROX_2->avg_ratio, 2);
            }
            if (count > 0)
                this->data_APPROX_2->deviation_ratio = sqrtl(total_sum / count);
            else
                this->data_APPROX_2->deviation_ratio = -1;

            //runtime
            total_sum = 0;
            this->data_APPROX_2->count_runtime = (long double)this->APPROX_2.size();
            for (SingleCalcDetail *item : this->APPROX_2)
                total_sum += item->get_runtime();
            this->data_APPROX_2->avg_runtime = total_sum / this->data_APPROX_2->count_runtime;

            total_sum = 0;
            for (SingleCalcDetail *item : this->APPROX_2)
                total_sum += pow(item->get_runtime() - this->data_APPROX_2->avg_runtime, 2);
            this->data_APPROX_2->deviation_runtime = sqrtl(total_sum / this->data_APPROX_2->count_runtime);
        }
        else
        {
            this->data_APPROX_2->avg_ratio = -1;
            this->data_APPROX_2->deviation_ratio = -1;
            this->data_APPROX_2->avg_runtime = -1;
            this->data_APPROX_2->deviation_runtime = -1;
        }
    }

    string Runtime_toString()
    {
        string output = "vertex count: " + to_string(this->vCount);
        output += "\n\tCNF-SAT:\n";
        output += this->data_CNF->Runtime_toString();
        output += "\n\tAPPROX-1:\n";
        output += this->data_APPROX_1->Runtime_toString();
        output += "\n\tAPPROX-2:\n";
        output += this->data_APPROX_2->Runtime_toString();
        return output;
    }
    string Ratio_toString()
    {
        string output = "vertex count: " + to_string(this->vCount);
        output += "\n\tCNF-SAT:\n";
        output += this->data_CNF->Ratio_toString();
        output += "\n\tAPPROX-1:\n";
        output += this->data_APPROX_1->Ratio_toString();
        output += "\n\tAPPROX-2:\n";
        output += this->data_APPROX_2->Ratio_toString();
        return output;
    }
};

// ------------------------ Global Variables ------------------------ //
int v_Count = 0;
bool calc_mode = false;
Graph *graph = new Graph();
Graph *graph_approx_1 = new Graph();
Graph *graph_approx_2 = new Graph();
pthread_t cnf_sat_vc, approx_vc_1, approx_vc_2;
long double time_cnf_sat, time_approx1, time_approx2;

vector<int> result_cnf, result_approx_1, result_approx_2;

vector<CalcStorage *> calc_data;
bool hasTimedOut = false;

// ------------------------ Time Execution related Functions ------------------------ //
static long double pclock(clockid_t cid)
{
    struct timespec ts;
    if (clock_gettime(cid, &ts) == -1)
        handle_error("clock_gettime");

    return (ts.tv_sec * 1000000) + (ts.tv_nsec / 1000);
}

// ------------------------ Approximation Ratio related Functions ------------------------ //
static long double approx_ratio(float input, float base)
{
    if (base == 0 && input == 0)
        return 1;
    else if (base == 0 && input != 0)
        return -1;
    return input / base;
}

// ------------------------ 3 Solvers Implementation ------------------------ //
// CNF-SAT-VC
void *CNF_SAT_VC(void *arg)
{
    // Initializing min, max
    int min = 1, max = v_Count;

    std::unique_ptr<Minisat::Solver> solver(new Minisat::Solver());
    int n = v_Count;
    //for (int k = v_Count - graph_degree-2; k <= v_Count; k++)
    int k;
    while (min <= max)
    {
        k = (min + max) / 2;
        // creating the literal table
        vector<vector<Minisat::Lit>> literals_table;

        vector<Minisat::Lit> tempRow;
        for (int i = 0; i < n; i++)
        {
            tempRow.clear();
            for (int j = 0; j < k; j++)
            {
                tempRow.push_back(Minisat::mkLit(solver->newVar()));
            }
            literals_table.push_back(tempRow);
        }

        Minisat::vec<Minisat::Lit> tempClause;
        // Reduction: part 1
        for (int j = 0; j < k; j++)
        {
            tempClause.clear();
            for (int i = 0; i < n; i++)
            {
                tempClause.push(literals_table[i][j]);
            }
            solver->addClause(tempClause);
        }

        // Reduction: part 2
        for (int m = 0; m < n; m++)
        {
            for (int q = 1; q < k; q++)
            {
                for (int p = 0; p < q; p++)
                    solver->addClause(~literals_table[m][p], ~literals_table[m][q]);
            }
        }

        // Reduction: part 3
        for (int m = 0; m < k; m++)
        {
            for (int q = 1; q < n; q++)
            {
                for (int p = 0; p < q; p++)
                    solver->addClause(~literals_table[p][m], ~literals_table[q][m]);
            }
        }

        // Reduction: part 4
        for (Node *i_item : graph->get_nodes())
        {
            for (Node *j_item : i_item->get_nodes())
            {
                int i_id = i_item->get_id();
                int j_id = j_item->get_id();
                if (i_id < j_id)
                {
                    tempClause.clear();
                    for (int j = 0; j < k; j++)
                    {
                        tempClause.push(literals_table[i_id][j]);
                        tempClause.push(literals_table[j_id][j]);
                    }
                    solver->addClause(tempClause);
                }
            }
        }

        bool res = solver->solve();
        if (res == 0)
        {
            min = k + 1;
        }
        else
        {
            max = k - 1;
            result_cnf.clear();
            for (int i = 0; i < n; i++)
            {
                for (int j = 0; j < k; j++)
                {
                    if (Minisat::toInt(solver->modelValue(literals_table[i][j])) == 0)
                    {
                        result_cnf.push_back(i);
                        break;
                    }
                }
            }
        }

        //de-allocates existing solver and allocates a new one in its place.
        solver.reset(new Minisat::Solver());
    }
    //Calc Mode
    if (calc_mode == true)
    {
        clockid_t cid;
        int s = pthread_getcpuclockid(cnf_sat_vc, &cid);
        if (s != 0)
        {
            handle_error_en(s, "pthread_getcpuclockid");
        }
        time_cnf_sat = pclock(cid);
    }
    return NULL;
}

// APPROX_VC_1
void *APPROX_VC_1(void *arg)
{
    result_approx_1.clear();
    while (graph_approx_1->degree() > 0)
    {
        Node *target = graph_approx_1->degreeNode();
        result_approx_1.push_back(target->get_id());
        for (Node *item : target->get_nodes())
            graph_approx_1->DisconnectNodes(target, item);
    }

    //Calc Mode
    if (calc_mode == true)
    {
        clockid_t cid;
        int s = pthread_getcpuclockid(approx_vc_1, &cid);
        if (s != 0)
        {
            handle_error_en(s, "pthread_getcpuclockid");
        }
        time_approx1 = pclock(cid);
    }
    return NULL;
}

// APPROX_VC_2
void *APPROX_VC_2(void *arg)
{
    vector<int> result;
    result_approx_2.clear();
    while (graph_approx_2->degree() > 0)
    {
        //selecting a node with the highest degree in our graph
        Node *target_1 = graph_approx_2->degreeNode();

        //selecting a node with the highest degree among all nodes that are connected to the target_1 node
        int temp_degree = 0;
        Node *target_2;
        for (Node *item : target_1->get_nodes())
        {
            if (temp_degree < item->degree())
            {
                temp_degree = item->degree();
                target_2 = item;
            }
        }

        result_approx_2.push_back(target_1->get_id());
        result_approx_2.push_back(target_2->get_id());

        for (Node *item : target_1->get_nodes())
            graph_approx_2->DisconnectNodes(target_1, item);

        for (Node *item : target_2->get_nodes())
            graph_approx_2->DisconnectNodes(target_2, item);
    }

    //Calc Mode
    if (calc_mode == true)
    {
        clockid_t cid;
        int s = pthread_getcpuclockid(approx_vc_2, &cid);
        if (s != 0)
        {
            handle_error_en(s, "pthread_getcpuclockid");
        }
        time_approx2 = pclock(cid);
    }
    return NULL;
}

// ------------------------ Calc Function ------------------------ //
static void Calc()
{
    // calc mode
    bool isExist = false;
    CalcStorage *cur;
    for (CalcStorage *item : calc_data)
    {
        if (item->vCount == v_Count)
        {
            isExist = true;
            cur = item;
            break;
        }
    }
    if (!isExist)
    {
        cur = new CalcStorage(v_Count);
        calc_data.push_back(cur);
    }
    if (!hasTimedOut)
    {
        cur->add_cnf(new SingleCalcDetail(1, time_cnf_sat));
        cur->add_app1(new SingleCalcDetail(approx_ratio(float(result_approx_1.size()), float(result_cnf.size())), time_approx1));
        cur->add_app2(new SingleCalcDetail(approx_ratio(float(result_approx_2.size()), float(result_cnf.size())), time_approx2));
    }
    else
    {
        cur->add_app1(new SingleCalcDetail(time_approx1));
        cur->add_app2(new SingleCalcDetail(time_approx2));
    }
}
// ------------------------ Printer Function ------------------------ //
static void Printer()
{
    //CNF-SAT-VC
    string output = "CNF-SAT-VC: ";
    if (hasTimedOut)
    {
        output += "timeout\n";
    }
    else
    {
        sort(result_cnf.begin(), result_cnf.end());
        for (int id : result_cnf)
        {
            output += to_string(id) + ",";
        }
        output = output.substr(0, output.length() - 1) + "\n";
    }

    //APPROX-VC-1
    output += "APPROX-VC-1: ";
    sort(result_approx_1.begin(), result_approx_1.end());
    for (int id : result_approx_1)
    {
        output += to_string(id) + ",";
    }
    output = output.substr(0, output.length() - 1) + "\n";

    //APPROX-VC-2
    output += "APPROX-VC-2: ";
    sort(result_approx_2.begin(), result_approx_2.end());
    for (int id : result_approx_2)
    {
        output += to_string(id) + ",";
    }
    output = output.substr(0, output.length() - 1) + "\n";

    cout << output;
}

// ------------------------ IO Thread ------------------------ //
void *I_O(void *arg)
{
    char cmd;
    while (!cin.eof())
    {

        string line;
        getline(cin, line);

        istringstream input(line);
        input >> cmd;
        if (input.eof())
            break;

        string edges;
        switch (cmd)
        {
        case 'V':
        {
            input >> v_Count;
            graph->clear();
            graph_approx_1->clear();
            graph_approx_2->clear();
            graph->fill(v_Count);
            graph_approx_1->fill(v_Count);
            graph_approx_2->fill(v_Count);
            break;
        }
        case 'E':
        {
            bool hasVertex = false;
            input >> edges;
            for (string item : parser(edges))
            {
                int seperator = item.find(",");
                int node1_id = stoi(item.substr(1, seperator - 1));
                int node2_id = stoi(item.substr(seperator + 1, item.length() - (seperator + 2)));
                if (node1_id == node2_id)
                {
                    cout << "Error: a node can't get connected to itself" << endl;
                    break;
                }
                if (node1_id >= v_Count || node1_id < 0 || node2_id >= v_Count || node2_id < 0)
                {
                    cout << "Error: node number is out of range" << endl;
                    break;
                }
                graph->ConnectNodes(graph->findNode(node1_id), graph->findNode(node2_id));
                graph_approx_1->ConnectNodes(graph_approx_1->findNode(node1_id), graph_approx_1->findNode(node2_id));
                graph_approx_2->ConnectNodes(graph_approx_2->findNode(node1_id), graph_approx_2->findNode(node2_id));
                hasVertex = true;
            }

            hasTimedOut = false;
            if (hasVertex)
            {
                pthread_create(&cnf_sat_vc, NULL, &CNF_SAT_VC, NULL);
                pthread_create(&approx_vc_1, NULL, &APPROX_VC_1, NULL);
                pthread_create(&approx_vc_2, NULL, &APPROX_VC_2, NULL);

                struct timespec ts;

                if (clock_gettime(CLOCK_REALTIME, &ts) == -1)
                {
                    handle_error("CLOCK_REALTIME");
                }
                ts.tv_sec += 10;
                int s = pthread_timedjoin_np(cnf_sat_vc, NULL, &ts);
                if (s != 0)
                {
                    hasTimedOut = true;
                    result_cnf.clear();
                }
                pthread_join(approx_vc_1, NULL);
                pthread_join(approx_vc_2, NULL);
            }
            else
            {
                result_cnf.clear();
                result_approx_1.clear();
                result_approx_2.clear();
            }
            if (calc_mode)
                Calc();

            Printer();

            break;
        }
        default:
            cout << "Error: invalid argument" << endl;
        }
    }
    return NULL;
}

// Main Program
int main(int argc, char *argv[])
{
    if (argc == 2)
        if (strcmp(argv[1], "-calc") == 0)
            calc_mode = true;

    pthread_t _io;
    pthread_create(&_io, NULL, &I_O, NULL);
    pthread_join(_io, NULL);
    if (calc_mode)
    {
        for (CalcStorage *item : calc_data)
        {
            item->calc();
        }
        cout << "=================== Calc Mode Start ===================" << endl;
        cout << "========= Ratio =========" << endl;
        for (CalcStorage *item : calc_data)
        {
            cout << item->Ratio_toString() << endl;
            cout << "---------------" << endl;
        }
        cout << "========= Runtime =========" << endl;
        for (CalcStorage *item : calc_data)
        {
            cout << item->Runtime_toString() << endl;
            cout << "---------------" << endl;
        }
        cout << "=================== Calc Mode End ===================" << endl;
    }

    delete graph;
    delete graph_approx_1;
    delete graph_approx_2;
    return 0;
}
