#include <iostream>
#include <algorithm>
#include <fstream>
#include <string>
#include <vector>
#include <cmath>

using ushort = unsigned short;
using MintermsList = std::vector<ushort>;
using OutputMintermsList = std::vector<MintermsList>;
using InputLabels = std::vector<std::string>;
using CanonicalMinterms = std::vector<std::string>;
using CanonicalOutput = std::vector<CanonicalMinterms>;
using ListPos = MintermsList::iterator;
using Labelpos = InputLabels::iterator;
using OutputLabels = InputLabels;
using NumberList = std::vector<ushort>;

struct Prime_Implicant{
    NumberList minterms;
    std::string simplified_number;
    bool was_combined = false;
};

using BitGroup = std::vector<Prime_Implicant>;
using MasterTable = std::vector <BitGroup>;
using ImplicantTable = std::vector<std::vector<bool>>;

MasterTable* groupByBits(MasterTable&);
ushort countBits(std::string&);
bool isSameTable(MasterTable&, MasterTable*);
std::string numberToExtendedBinaryString(ushort, ushort);
void setBinaryExpressionZeros(std::string&, ushort);
int getUniqueChangePosition(std::string&, std::string&);
std::string setDontCareBit(std::string, unsigned short);
void getImplicantFromMaster(MasterTable&, BitGroup&);
BitGroup makeImplicantTable(MasterTable&, NumberList&,ImplicantTable&);
int findFirstMintermFromList(NumberList&, ushort);
std::string getLettersFromImplicants(std::string &, ushort, InputLabels &);
bool existInTable(BitGroup&, std::string&);
void makeMasterTable(MasterTable&, ushort);
int initReduction(NumberList &, ushort, MasterTable &, InputLabels &);
bool existInTable(BitGroup&, int);
bool isValidFile(std::string&);
void generateDefaultLabels(InputLabels&, std::string&&, ushort);
void makeVariableLetterList(InputLabels&, std::string&, std::string&, ushort);
void makeMintermsList(MintermsList& list, std::string&, std::string&, ushort);
void setBinaryExpressionZeros(std::string&, ushort);
std::string numberToExtendedBinaryString(ushort, ushort);
std::string getLettersFromMinterms(std::string&, InputLabels&);
void makeSOPForm(CanonicalMinterms&, MintermsList&, InputLabels&, ushort);
void makeCanonicalOutput(CanonicalOutput&, OutputMintermsList&, InputLabels&, ushort);
void printCanonicalForm(CanonicalOutput&, OutputLabels&);

int main(int argc, char *argv[]) {
    using namespace std;
    ifstream table_file;
    string file_name, file_content, pattern;
    OutputMintermsList output_list;
    InputLabels input_variable_labels;
    OutputLabels output_variable_labels;
    CanonicalOutput SOP_form;
    bool valid_file_was_found = false;
    size_t i, input_size;
    MasterTable table;
    if(argc > 3){
        for(i = 0; i < argc; ++i){
            file_name = argv[i];
            valid_file_was_found = isValidFile(file_name);
            if(valid_file_was_found){
                break;
            }
        }
        if(valid_file_was_found){
            if((argc - i) != 2){
                table_file.open(file_name);
                if(table_file.is_open()){
                    pattern = argv[i + 1];
                    input_size = std::stol(argv[i + 2]);
                    if(input_size != 0){
                        i = 0;
                        getline(table_file, file_content);
                        while(!table_file.eof() && i < input_size){
                            output_list.push_back(MintermsList());
                            makeMintermsList(output_list[i], file_content, pattern, static_cast<size_t>(pow(2, input_size)) - 1);
                            ++i;
                            getline(table_file, file_content);
                        }
                        if(!file_content.empty())
                            makeVariableLetterList(input_variable_labels, file_content, pattern, input_size);
                        else
                            generateDefaultLabels(input_variable_labels, "x", input_size);
                        generateDefaultLabels(output_variable_labels, "S", output_list.size());
                        makeCanonicalOutput(SOP_form, output_list, input_variable_labels, input_size);
                        printCanonicalForm(SOP_form, output_variable_labels);
                        for(int k = 0; k < output_list.size(); ++k){
                            cout << endl;
                            makeMasterTable(table, input_size + 1);
                            cout << output_variable_labels[k] << " = ";
                            initReduction(output_list[k], input_size, table, input_variable_labels);
                        }
                    }
                    else{
                        cerr << "Invalid input size" << endl;
                    }
                }
                else
                    cout << "Failed while opening file, exit program" << endl;
            }
            else
                cout << "Not enough arguments" << endl;
        }
        else
            cout << "Valid file was not found" << endl;
    }
    else
        cout << "Not enough arguments" << endl;
    return 0;
}

void makeMasterTable(MasterTable& table, ushort size){
    table.clear();
    for(int i = 0; i < size; ++i){
        table.push_back(BitGroup());
    }
}

int initReduction(NumberList &minterms, ushort input_size, MasterTable &table, InputLabels &input_label) {
    Prime_Implicant tmp;
    MasterTable *tmp_table;
    ImplicantTable implicant_table;
    BitGroup essential_implicants;
    //First Iteration
    for(auto& i : minterms){
        tmp.minterms.push_back(i);
        tmp.simplified_number = numberToExtendedBinaryString(i, input_size);
        table[countBits(tmp.simplified_number)].push_back(tmp);
        tmp.minterms.clear();
    }
    //Second Iteration
    while(table.size() >= 2){
        tmp_table = groupByBits(table);
        if(!isSameTable(table, tmp_table)){
            table = *tmp_table;
            delete tmp_table;
            tmp_table = nullptr;
        }
        else
            break;
    }
    essential_implicants = makeImplicantTable(table, minterms, implicant_table);

    if(!essential_implicants.empty()){
        for(int i = 0; i < essential_implicants.size(); ++i){
            if(!existInTable(essential_implicants, i)){
                std::cout << getLettersFromImplicants(essential_implicants[i].simplified_number, input_size,
                                                      input_label);
                if(i != essential_implicants.size() - 1)
                    std::cout << " + ";
            }
        }
    }
    else{
        BitGroup implicants;
        NumberList points(implicants.size(), 0);
        int position = 0;
        getImplicantFromMaster(table, implicants);
        //Deletes all minterms reached by prime implicants
        for(int i = 0; i < implicants.size(); ++i){
            for(int j = 0; j < implicants[i].minterms.size(); ++j){
                for(int k = i + 1; k < implicants.size() - 1; ++k)
                    for(int l = 0; l < implicants[k].minterms.size(); ++l)
                        if(implicants[i].minterms[j] == implicants[k].minterms[l])
                            implicants.erase(implicants.begin() + k);
            }
        }
        for(int i = 0; i < implicants.size(); ++i){
            if(!existInTable(implicants, i))
                std::cout << getLettersFromImplicants(implicants[i].simplified_number, input_size, input_label);
            if(i != implicants.size() - 1)
                std::cout << " + ";
        }
    }
    return -1;
}

bool existInTable(BitGroup& implicants, int start){
    for(int i = start + 1; i < implicants.size(); ++i){
        if(implicants[i].simplified_number == implicants[start].simplified_number)
            return true;
    }
    return false;
}

MasterTable* groupByBits(MasterTable &master){
    auto* tmp_master_table = new MasterTable(master.size());
    Prime_Implicant tmp_implicant;
    int position;
    //Index Groups
    for(int i = 0; i < master.size() - 1; ++i){
        //Index Minterms for i
        for(int j = 0; j < master[i].size(); ++j){
            //Index Minterms for i + 1
            for(int k = 0; k < master[i + 1].size(); ++k){
                position = getUniqueChangePosition(master[i][j].simplified_number, master[i + 1][k].simplified_number);
                if(position != -1) {
                    tmp_implicant.minterms.insert(tmp_implicant.minterms.end(), master[i][j].minterms.begin(), master[i][j].minterms.end());
                    tmp_implicant.minterms.insert(tmp_implicant.minterms.end(), master[i + 1][k].minterms.begin(), master[i + 1][k].minterms.end());
                    tmp_implicant.simplified_number = setDontCareBit(master[i][j].simplified_number, position);
                    tmp_implicant.was_combined = false;
                    master[i][j].was_combined = true;
                    master[i + 1][k].was_combined = true;
                    if(!existInTable((*tmp_master_table)[i], tmp_implicant.simplified_number))
                        (*tmp_master_table)[i].push_back(tmp_implicant);
                    tmp_implicant.minterms.clear();
                }
            }
        }
    }

    for(auto& i : master)
        for(auto& j : i)
            if(!j.was_combined)
                (*tmp_master_table)[countBits(j.simplified_number)].push_back(j);
    return tmp_master_table;
}

bool existInTable(BitGroup & table, std::string& data){
    for(auto& i : table)
        if(i.simplified_number == data)
            return true;
    return false;
}

BitGroup makeImplicantTable(MasterTable& master, NumberList& minterms_list,ImplicantTable& implicant_table){
    //Initialize implicant table
    int position = 0;
    BitGroup prime_implicants, essential_prime_implicants;
    getImplicantFromMaster(master, prime_implicants);
    std::vector<bool> tmp_implicant_row(prime_implicants.size(), false);
    for(int i = 0; i < minterms_list.size(); ++i){
        implicant_table.push_back(tmp_implicant_row);
    }
    //Fills with prime implicants
    for(int i = 0; i < prime_implicants.size(); ++i)
        for(auto& j : prime_implicants[i].minterms)
            implicant_table[findFirstMintermFromList(minterms_list, j)][i] = true;
    //Analyze rows
    int unique_truth = -1;
    bool was_changed = false;
    for(auto & i : implicant_table){
        for(int j = 0; j < i.size(); ++j){
            if(i[j]){
                if(!was_changed){
                    unique_truth = j;
                    was_changed = true;
                }
                else{
                    unique_truth = -1;
                    break;
                }
            }
        }
        if(unique_truth != -1)
            essential_prime_implicants.push_back(prime_implicants[unique_truth]);
        was_changed = false;
    }
    //Deletes all minterms reached by essential prime implicants
    for(int i = 0; i < essential_prime_implicants.size(); ++i){
        for(int j = 0; j < essential_prime_implicants[i].minterms.size(); ++j){
            position = findFirstMintermFromList(minterms_list, essential_prime_implicants[i].minterms[j]);
            if(position != -1)
                minterms_list.erase(minterms_list.begin() + position);
        }
    }
    //Match for residual essential minterms
    NumberList points(prime_implicants.size(), 0);
    if(minterms_list.size() != 0){
        for(int i = 0; i < minterms_list.size(); ++i){
            for(int j = 0; j < prime_implicants.size(); ++j)
                for(int k = 0; k < prime_implicants[j].minterms.size(); ++k)
                    points[j] += (prime_implicants[j].minterms[k] == minterms_list[i]) ? 1 : 0;
        }
        //Push residual essenstial minterms
        for(int j = 0; j < points.size(); ++j)
            if(points[j] == minterms_list.size())
                essential_prime_implicants.push_back(prime_implicants[j]);
    }
    return essential_prime_implicants;
}

void getImplicantFromMaster(MasterTable& master, BitGroup& prime_implicants_list){
    for(auto& i : master)
        for(auto& j : i)
            prime_implicants_list.push_back(j);
}

bool isSameTable(MasterTable& table, MasterTable* tmp_master){
    try{
        for(int i = 0; i < table.size(); ++i){
            for(int j = 0; j < table[i].size(); ++j)
                if(table[i][j].simplified_number != (*tmp_master)[i][j].simplified_number)
                    return false;
        }
        return true;
    }catch(std::out_of_range& e){
        return false;
    }
}

ushort countBits(std::string& number){
    ushort bit_count = 0;
    for(auto& i : number)
        bit_count += (i == '1');
    return bit_count;
}

int getUniqueChangePosition(std::string& binary_expression1, std::string& binary_expression2){
    int position = 0;
    bool was_changed_before = false;
    for(int i = 0; i < binary_expression1.size(); ++i)
        if(binary_expression1[i] != binary_expression2[i]){
            if (!was_changed_before) {
                position = i;
                was_changed_before = true;
            }
            else
                return -1;
        }
    return position;
}

std::string setDontCareBit(std::string binary_expression, unsigned short position){
    binary_expression[position] = '-';
    return binary_expression;
}

int findFirstMintermFromList(NumberList& minterms, ushort minterm){
    for(int i = 0; i < minterms.size(); ++i)
        if(minterms[i] == minterm)
            return i;
    return -1;
}

void printImplicantTable(ImplicantTable & table){
    for(auto& i : table){
        for(auto && j : i)
            std::cout << j << " ";
        std::cout << std::endl;
    }

}

std::string getLettersFromImplicants(std::string &binary_expression, ushort variable_number, InputLabels &input_label) {
    std::string products;
    for(int i = 0; i < binary_expression.size(); ++i){
        if(binary_expression[i] != '-'){
            products += input_label[i];
            if(binary_expression[i] == '0')
                products += '\'';
        }
    }
    return products;
}

bool isValidFile(std::string& argument){
    if(argument.find(".txt") != std::string::npos)
        return true;
    return false;
}

void generateDefaultLabels(InputLabels& list, std::string&& default_label, ushort max_size){
    for(int i = 0; i < max_size; ++i)
        list.push_back(default_label + std::to_string(i));
}

void makeVariableLetterList(InputLabels& list, std::string& file_content, std::string& pattern, ushort max_minterm){
    size_t pattern_pos = 0, max_size = max_minterm;
    Labelpos letter_pos;
    InputLabels letter_list;
    std::string label;
    while(pattern_pos != std::string::npos){
        pattern_pos = file_content.find(pattern);
        label = file_content.substr(0, pattern_pos);
        letter_pos = std::find(list.begin(), list.end(), label);
        if(letter_pos == list.end() && max_minterm > 0){
            list.push_back(label);
            --max_minterm;
        }
        file_content.erase(0,pattern_pos + 1);
    }
    if(list.size() != max_size){
        while(max_minterm > 0){
            list.push_back("x" + std::to_string(max_minterm));
            --max_minterm;
        }
    }
    std::sort(list.begin(), list.end());
}

void makeMintermsList(MintermsList& list, std::string& file_content, std::string& pattern, ushort max_minterm){
    size_t pattern_pos = 0;
    ListPos minterm_pos;
    InputLabels letter_list;
    ushort minterm;
    while(pattern_pos != std::string::npos) {
        pattern_pos = file_content.find(pattern);
        minterm = std::stoi(file_content.substr(0, pattern_pos));
        minterm_pos = std::find(list.begin(), list.end(), minterm);
        if (minterm_pos == list.end() && minterm <= max_minterm)
            list.push_back(minterm);
        file_content.erase(0, pattern_pos + 1);
    }
}

void setBinaryExpressionZeros(std::string& binary, ushort input_size){
    while(input_size-- > 0)
        binary += '0';
}

std::string numberToExtendedBinaryString(ushort number, ushort input_size){
    std::string binary_expression;
    setBinaryExpressionZeros(binary_expression, input_size);
    while(number != 0){
        binary_expression[(input_size--) - 1] = static_cast<char>(48 + (number % 2));
        number /= 2;
    }
    return binary_expression;
}

std::string getLettersFromMinterms(std::string& binary_expression, InputLabels& labels){
    std::string products;
    for(int i = 0; i < binary_expression.size(); ++i){
        products += labels[i];
        if(binary_expression[i] == '0')
            products += '\'';
    }
    return products;
}

void makeSOPForm(CanonicalMinterms& sop_form, MintermsList& list, InputLabels& input_labels, ushort input_size){
    for(int i = 0; i < list.size(); ++i){
        sop_form.push_back(numberToExtendedBinaryString(list[i], input_size));
        sop_form[i] = getLettersFromMinterms(sop_form[i], input_labels);
    }
}

void printCanonicalForm(CanonicalOutput& sop_form_list, OutputLabels& labels){
    using namespace std;
    for(int i = 0; i < sop_form_list.size(); ++i){
        cout << labels[i] << " = ";
        for(int j = 0; j < sop_form_list[i].size(); ++j){
            cout << sop_form_list[i][j];
            if(j != sop_form_list[i].size() - 1)
                cout << " + ";
            else
                cout << endl;
        }
    }
}

void makeCanonicalOutput(CanonicalOutput& sop_form, OutputMintermsList& minterms_list, InputLabels& input_labels, ushort input_size){
    for(int i = 0; i < minterms_list.size(); ++i){
        sop_form.push_back(CanonicalMinterms());
        makeSOPForm(sop_form[i], minterms_list[i], input_labels, input_size);
    }
}

