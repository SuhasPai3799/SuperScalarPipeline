/*****************************/
/*Suhas Pai*******************/
/*Version 2.1*****************/
/*Compile with g++ -std=c++14*/
/*****************************/
//Tomasulo algo
//Create reservation station
//Create ReOrder buffer
//Create ARF and RRF
//Rename registers before  inserting them into reservation stations
//Check if source registers are available
//Store index of instruction in reorder buffer
//Before writing back,update all fields that are using the tag of the current destination register
#include<bits/stdc++.h>
using namespace std;
#define ll long long
#define pb push_back
#define mp make_pair
#define INF -1000000000
map<char,ll> hexA;
int getDecFromHex(string str) //Converting Hexadecimal string to a long integer
{
    int res=0;
    for(auto it:str)
    {
        res*=16;

        res+=hexA[it];
    }
    return res;
}
string getHex(int num)
{
    string temp;
    char ch;
    if(num==0)
    {
        temp.push_back('0');
        temp.push_back('0');
        return  temp;
    }
    while(num>0)
    {
        if(num%16>=10)
        {
            temp.pb('A'+(num%16-10));
        }
        else
        {
            temp.pb('0'+num%16);
        }
        num/=16;
    }
    if(temp.size()==1)
        temp.push_back('0');
    reverse(temp.begin(),temp.end());
    return temp;
}
struct ReOrderNode {
    int order;
    int tag_d;
    bool busy;
    int cur_PC;
    int destination_reg;
    int value;
    bool valid;
    bool load;
    bool store;
    bool un_jump;
    int offset;
    bool con_jump;
    bool halt;
    ReOrderNode()
    {
        busy=true;
        valid=false;
        load=false;
        store=false;
        un_jump=false;
        con_jump=false;
        halt=false;
    }
};

struct RRF_Node {
    bool valid;
    bool busy;
    int resStation;
    ll data;
    RRF_Node() {
        valid=false;
        busy=false;
    }
};
struct ARF_Node {
    bool busy;
    ll tag;
    ll data;
    ARF_Node() {
        busy=false;
    }
};
struct ExecuteNode {
    int val1;
    int val2;
    int tag1;
    int tag2;
    int tag_d;
    string instr;
    int destination_reg;
    bool used;
    int result;
    int order;
    bool load;
    int cur_PC;
    bool store;
    bool halt;
    ExecuteNode() {
        used=false;
        load=false;
        store=false;
        halt=false;
    }
};
struct ResStationNode {
    int tag1;
    int tag2;
    int tag_d;
    int s1;
    int s2;
    int order;
    string instr;
    int destination_reg;
    int cur_PC;
    bool used;
    bool load;
    bool store;
    bool halt;
    ResStationNode() {
        used=false;
        load=false;
        store=false;
        halt=false;
    }
};
void renameDest(int reg,vector<ARF_Node> &ARF,vector<RRF_Node> &RRF)
{
    ARF[reg].busy=true;
    
    for(int i=0; i<32; i++)
    {
        if(RRF[i].busy==false)
        {
            RRF[i].busy=true;
            ARF[reg].tag=i;
            RRF[i].valid=false;
            break;
        }
    }
}
int PC=0;
vector<int> DataCache;
vector<pair<string,int>> InstructionBuffer;

vector<RRF_Node> RRF(32);
vector<ARF_Node> ARF(32);


vector<ResStationNode> ReservationStation(16);

int addLatency=1;
int MulLatency=1;
int LoadLatency=1;
int JumpLatency=1;
int addCtr=1;
int mulCtr=1;
int loadCtr=1;
int jumpCtr=1;
int logCtr=1;
vector<ExecuteNode> AddExec;
vector<ExecuteNode> MultExec;
vector<ExecuteNode> LoadStore;
vector<ExecuteNode> Jumps;
vector<ReOrderNode> ROB;
vector<ExecuteNode> CondJump;
vector<ExecuteNode> Halt;
vector<ExecuteNode> Logic;

int curResSize=0;
int stop_rem;
int con_stop_rem;
int ROB_Order=0;
bool jump=false;
bool con_jump=false;
int real_PC,con_real_PC;
bool stop=false;
bool set_jump=false;
bool set_con_jump=false;
int cycles=0;
int addLatency;
int mulLatency;

void TryExecute()
{
    if(Halt.size()>0)
    {
        ExecuteNode EN=Halt[0];
        for(ll i=0; i<ROB.size(); i++)
        {
            if(ROB[i].order==EN.order)
            {
                ROB[i].busy=false;
                ROB[i].valid=true;
                
                ROB[i].halt=true;
                break;
            }
        }
        Halt.erase(Halt.begin(),Halt.begin()+1);
    }
    if(Jumps.size()>0)
    {
        ExecuteNode EN=Jumps[0];
        
        int offset=16*EN.val1+EN.val2;
        if(offset>=128)
            offset-=256;
        bool f1=false;
        real_PC=EN.cur_PC+offset;
        jump=false;
        set_jump=true;
        stop_rem=ROB_Order;
        PC=real_PC;
        set_jump=false;
        for(ll i=0; i<ROB.size(); i++)
        {
            if(ROB[i].order==EN.order)
            {
                ROB[i].busy=false;
                ROB[i].valid=true;
                ROB[i].un_jump=true;
                f1=true;
                break;
            }
        }
        Jumps.erase(Jumps.begin(),Jumps.begin()+1);
    }
    if(CondJump.size()>0)
    {
        ExecuteNode EN=CondJump[0];
        cout<<EN.val1<<" "<<EN.instr<<"\n";
        if(EN.val1==0)
        {
        
            con_real_PC=EN.cur_PC+EN.val2;
            set_con_jump=true;
            con_jump=false;
            con_stop_rem=ROB_Order;
            PC=con_real_PC;
            set_con_jump=false;
        }
        else
        {
            set_con_jump=false;
            con_stop_rem=-1;
            con_jump=false;
        }
        
        for(ll i=0; i<ROB.size(); i++)
        {
            if(ROB[i].order==EN.order)
            {
                ROB[i].busy=false;
                ROB[i].valid=true;
                ROB[i].con_jump=true;
                break;
            }
        }
        CondJump.erase(CondJump.begin(),CondJump.begin()+1);
       
    }
    if(Logic.size())
    {
            ExecuteNode EN=Logic[0];
            if(EN.instr[0]=='4')
            EN.result=EN.val1&EN.val2;
            else if(EN.instr[0]=='5')
            EN.result=EN.val1 | EN.val2;
            else if(EN.instr[0]=='6')
            EN.result=256-(EN.val1);
            else
            EN.result=(EN.val1^EN.val2);
            int reg=EN.destination_reg;
            int reg_tag=EN.tag_d;
            RRF[reg_tag].valid=true;
            RRF[reg_tag].data=EN.result;
            for(ll i=0; i<16; i++)
            {
                if(ReservationStation[i].used && ReservationStation[i].tag1==reg_tag)
                {
                    ReservationStation[i].s1=EN.result;
                    ReservationStation[i].tag1=-1;

                }
                if(ReservationStation[i].used && ReservationStation[i].tag2 ==reg_tag)
                {
                    ReservationStation[i].s2=EN.result;
                    ReservationStation[i].tag2=-1;
                }
            }

            for(ll i=0; i<ROB.size(); i++)
            {
                if(ROB[i].order==EN.order)
                {
                    ROB[i].busy=false;
                    ROB[i].destination_reg=reg;
                    ROB[i].value=EN.result;
                    ROB[i].valid=true;
                    ROB[i].tag_d=EN.tag_d;

                    break;
                }
            }
    }
    if(MultExec.size()>0)
        {
            ExecuteNode EN=MultExec[0];
            EN.result=EN.val1*EN.val2;
            
            int reg=EN.destination_reg;
            int reg_tag=EN.tag_d;
            RRF[reg_tag].valid=true;
            RRF[reg_tag].data=EN.result;
            
            for(ll i=0; i<16; i++)
            {
                if(ReservationStation[i].used && ReservationStation[i].tag1==reg_tag)
                {
                    ReservationStation[i].s1=EN.result;
                    ReservationStation[i].tag1=-1;

                }
                if(ReservationStation[i].used && ReservationStation[i].tag2 ==reg_tag)
                {
                    ReservationStation[i].s2=EN.result;
                    ReservationStation[i].tag2=-1;
                }
            }

            for(ll i=0; i<ROB.size(); i++)
            {
                if(ROB[i].order==EN.order)
                {
                    ROB[i].busy=false;
                    ROB[i].destination_reg=reg;
                    ROB[i].value=EN.result;
                    ROB[i].valid=true;
                    ROB[i].tag_d=EN.tag_d;
                    break;
                }
            }
        }
        if(AddExec.size()>0)
        {
            
            ExecuteNode EN=AddExec[0];
            if(EN.instr[0]=='0' || EN.instr[0]=='3')
            EN.result=EN.val1+EN.val2;
            else if(EN.instr[0]=='1')
            EN.result=EN.val1-EN.val2;

            int reg=EN.destination_reg;
            int reg_tag=EN.tag_d;
            
            RRF[reg_tag].valid=true;
            RRF[reg_tag].data=EN.result;
            for(ll i=0; i<16; i++)
            {

                if(ReservationStation[i].used && ReservationStation[i].tag1==reg_tag)
                {
                    ReservationStation[i].s1=EN.result;
                    ReservationStation[i].tag1=-1;
                }
                if(ReservationStation[i].used && ReservationStation[i].tag2 ==reg_tag)
                {
                    ReservationStation[i].s2=EN.result;
                    ReservationStation[i].tag2=-1;
                }
            }
            for(ll i=0; i<ROB.size(); i++)
            {
                if(ROB[i].order==EN.order)
                {
                    ROB[i].busy=false;
                    ROB[i].destination_reg=reg;
                    ROB[i].value=EN.result;
                    ROB[i].valid=true;
                    ROB[i].tag_d=EN.tag_d;
                    break;
                }
            }
            AddExec.erase(AddExec.begin(),AddExec.begin()+1);
        }
        if(LoadStore.size())
        {
            ExecuteNode EN=LoadStore[0];
           
            if(EN.load)
            EN.result=DataCache[EN.val1+EN.val2];
            else
            {
                int offset=hexA[EN.instr[3]];
                EN.result=offset+EN.val1;
            }     
            if(EN.load)
            {
                int reg=EN.destination_reg;
                
                int reg_tag=EN.tag_d;
                
                RRF[reg_tag].valid=true;
                RRF[reg_tag].data=EN.result;
                for(ll i=0; i<16; i++)
                {
                if(ReservationStation[i].used && ReservationStation[i].tag1==reg_tag)
                    {
                        ReservationStation[i].s1=EN.result;
                        ReservationStation[i].tag1=-1;
                    }
                if(ReservationStation[i].used && ReservationStation[i].tag2 ==reg_tag)
                    {
                        ReservationStation[i].s2=EN.result;
                        ReservationStation[i].tag2=-1;
                    }
                }
                for(ll i=0; i<ROB.size(); i++)
                {
                    if(ROB[i].order==EN.order)
                    {   
                        ROB[i].busy=false;
                        ROB[i].destination_reg=reg;
                        ROB[i].value=EN.result;
                        ROB[i].valid=true;
                        ROB[i].tag_d=EN.tag_d;
                        break;
                    }
                }
            }
            else
            {
                for(ll i=0; i<ROB.size(); i++)
                {
                    if(ROB[i].order==EN.order)
                    {   
                        ROB[i].busy=false;
                        ROB[i].destination_reg=EN.val2;
                        ROB[i].value=EN.result;
                        ROB[i].valid=true;
                        break;
                    }
                }
            }
            
            
            LoadStore.erase(LoadStore.begin(),LoadStore.begin()+1);
        }

}
void MoveResToExecute()
{
    //Remove the instructions from reservation stations and push them into their execute stations if both their operands are available
        int mini=-INF;
        for(int i=0;i<16;i++)
        {
            if(ReservationStation[i].used)
            {
                if(ReservationStation[i].tag1==-1 && ReservationStation[i].tag2==-1)
                {
                    if((ReservationStation[i].instr[0]=='8' || ReservationStation[i].instr[0]=='9'))
                    {
                        mini=min(mini,ReservationStation[i].order);
                    }
                }
            }
        } 
        for(int i=0; i<16; i++)
        {
            
            if(ReservationStation[i].used==true)
            {
                
                if(ReservationStation[i].tag1==-1 && ReservationStation[i].tag2==-1)
                {
                    
                    ExecuteNode EA;
                    EA.val1=ReservationStation[i].s1;
                    EA.val2=ReservationStation[i].s2;
                    EA.tag1=ReservationStation[i].tag1;
                    EA.tag2=ReservationStation[i].tag2;
                    EA.destination_reg=ReservationStation[i].destination_reg;
                    EA.order=ReservationStation[i].order;
                    EA.tag_d=ReservationStation[i].tag_d;
                    EA.load=ReservationStation[i].load;
                    EA.store=ReservationStation[i].store;
                    EA.instr=ReservationStation[i].instr;
                    EA.halt=ReservationStation[i].halt;
                    if(AddExec.size()==0 && (ReservationStation[i].instr[0]=='0' || ReservationStation[i].instr[0]=='1' || ReservationStation[i].instr[0]=='3'))
                    {
                        AddExec.push_back(EA);
                        
                        ReservationStation[i].used=false;
                        ReservationStation[i].load=false;
                        ReservationStation[i].store=false;
                        ReservationStation[i].halt=false;
                        curResSize--;
                    }
                    else if(MultExec.size()==0 && ReservationStation[i].instr[0]=='2')
                    {

                        MultExec.push_back(EA);
                        ReservationStation[i].used=false;
                        ReservationStation[i].load=false;
                        ReservationStation[i].store=false;
                        ReservationStation[i].halt=false;
                        curResSize--;
                    }
                    else if(LoadStore.size()==0 && (ReservationStation[i].instr[0]=='8' || ReservationStation[i].instr[0]=='9') && ReservationStation[i].order==mini)
                    {
                        
                        LoadStore.push_back(EA);
                        ReservationStation[i].used=false;
                        ReservationStation[i].load=false;
                        ReservationStation[i].store=false;
                        ReservationStation[i].halt=false;
                        curResSize--;
                    }
                    else if(Jumps.size()==0 && ReservationStation[i].instr[0]=='A')
                    {
                        EA.cur_PC=ReservationStation[i].cur_PC;
                        Jumps.push_back(EA);
                        ReservationStation[i].used=false;
                        ReservationStation[i].load=false;
                        ReservationStation[i].store=false;
                        ReservationStation[i].halt=false;
                        curResSize--;
                    }
                    else if(CondJump.size()==0 && ReservationStation[i].instr[0]=='B')
                    {
                        EA.cur_PC=ReservationStation[i].cur_PC;
                        
                        CondJump.push_back(EA);
                        ReservationStation[i].used=false;
                        ReservationStation[i].load=false;
                        ReservationStation[i].store=false;
                        ReservationStation[i].halt=false;
                        curResSize--;
                    }
                    else if(Halt.size()==0 && ReservationStation[i].instr[0]=='F')
                    {
                        Halt.push_back(EA);
                        ReservationStation[i].used=false;
                        ReservationStation[i].load=false;
                        ReservationStation[i].store=false;
                        ReservationStation[i].halt=true;
                        
                        curResSize--;
                    }
                    else if(Logic.size()==0 && hexA[ReservationStation[i].instr[0]]>=4 && hexA[ReservationStation[i].instr[0]]<=7)
                    {
                        Logic.push_back(EA);
                        ReservationStation[i].used=false;
                        ReservationStation[i].load=false;
                        ReservationStation[i].store=false;
                        ReservationStation[i].halt=false;
                        curResSize--;
                    }
                }
            }
        }
}

int main()
{
    hexA['0']=0;
    hexA['1']=1;
    hexA['2']=2;
    hexA['3']=3;
    hexA['4']=4;
    hexA['5']=5;
    hexA['6']=6;
    hexA['7']=7;
    hexA['8']=8;
    hexA['9']=9;
    hexA['A']=10;
    hexA['B']=11;
    hexA['C']=12;
    hexA['D']=13;
    hexA['E']=14;
    hexA['F']=15;

    ifstream IC("ICache.txt");
    vector<string> InstCache;
    string str;
    while(IC>>str)
    {
        InstCache.pb(str);
    }

    
    ifstream DC("DCache.txt");
    string num;
    int stalls=0;
    while(DC>>num)
    {
        if(getDecFromHex(num)<128)
        DataCache.pb(getDecFromHex(num));
        else
        {
            DataCache.pb(getDecFromHex(num)-256);
        }
        
    }
    ifstream RF("RF.txt");
    
    int ctr=0;
    while(RF>>num)
    {
        int val=getDecFromHex(num);
        if(val>=128)
        val-=256;
        ARF[ctr].data=val;
        ARF[ctr].tag=0;
        ARF[ctr].busy=false;
        ctr++;
    }
    int instructions=0;
    bool IB_Lock=false;
    
    int ins=0;
    while(cycles<50)
    {
        cycles++;
        cout<<Jumps.size()<<" "<<CondJump.size()<<"\n";
        ll mini=-INF;
        ll index=-1;
        bool flag=true;
        mini=-INF;
        index=-1;
        for(ll i=0; i<ROB.size(); i++)
        {
            
            if(ROB[i].valid==true && ROB[i].busy==false)
            {
                if(ROB[i].order<mini)
                {
                    mini=ROB[i].order;
                    index=i;
                }
            }
        }
        
        if(mini!=-INF)
        {
            
            instructions++;
            if(ROB[index].halt)
            {
                
                break;
            }
            else if(ROB[index].store)
            {
                DataCache[ROB[index].value]=ROB[index].destination_reg;
                ROB.erase(ROB.begin()+index);
            }
            else if(ROB[index].con_jump)
            {
                
                
                    ROB.erase(ROB.begin()+index);
            
            }
            else if(ROB[index].un_jump)
            {
                
                vector<ReOrderNode> temp;
                
                for(auto it:ROB)
                {
                    if(!it.store && !it.un_jump &&!it.con_jump && it.order<stop_rem)
                    {
                        ll dreg=ROB[index].destination_reg;
                        if(dreg>=0 && dreg<ARF.size())
                        ARF[dreg].busy=false;
                    }
                    else if(it.order>=stop_rem)
                    {
                        temp.push_back(it);
                    }
                }
                ROB.clear();
                for(auto it:temp)
                {
                    ROB.push_back(it);
                }
            }
            else
            {
                
                ll dreg=ROB[index].destination_reg;
                if(ARF[dreg].tag==ROB[index].tag_d)
                {
                    ARF[dreg].data=ROB[index].value;
                    ARF[dreg].busy=false;
                }
                
                ROB.erase(ROB.begin()+index);
            }
            flag=true;
            
        
        }
        else
        {
            stalls++;
        }
        
        
        TryExecute();
        
        MoveResToExecute();
        
        
        //Push instructions into reservation stations
        if(InstructionBuffer.size()>0)
        {
            string inst=InstructionBuffer[0].first;
            int opCode=hexA[inst[0]];
          
            //cout<<opCode<<"\n";
            if(curResSize<16)
            {
                ResStationNode node;
                if(opCode==15)
                {
                    
                    node.instr=inst;
                    node.order=ROB_Order;
                    ROB_Order++;
                    node.tag1=-1;
                    node.tag2=-1;
                    bool flag=false;
                    for(int i=0; i<16; i++)
                    {
                        if(ReservationStation[i].used==false)
                        {
                            ReservationStation[i]=node;
                            ReservationStation[i].used=true;
                            curResSize++;
                            flag=true;
                            break;
                        }
                    }
                    if(flag)
                    {
                        ReOrderNode RB;
                        RB.busy=true;
                        
                        RB.order=node.order;
                    
                        RB.valid=false;
                        RB.halt=true;
                        ROB.push_back(RB);
                        InstructionBuffer.erase(InstructionBuffer.begin(),InstructionBuffer.begin()+1);
                    }
                }
                else if(opCode==11)
                {
                    node.instr=inst;
                    con_jump=true;
                    node.order=ROB_Order;
                    ROB_Order++;
                    node.tag2=-1;
                    node.s2=16*hexA[inst[2]]+hexA[inst[3]];
                    if(node.s2>=128)
                    node.s2-=256;
                    node.s1=-1;
                    node.cur_PC=InstructionBuffer[0].second;
                    int r1=hexA[inst[1]];
                    if(!ARF[r1].busy)
                    {
                        node.s1=ARF[r1].data;
                        node.tag1=-1;
                    }
                    else
                    {

                        int mappedReg=ARF[r1].tag;
                        if(RRF[mappedReg].valid)
                        {
                            node.s1=RRF[mappedReg].data;
                            node.tag1=-1;
                        }
                        else
                        {
                            node.s1=INF;
                            node.tag1=mappedReg;
                        }

                    }
                    bool flag=false;
                    for(int i=0; i<16; i++)
                    {
                        if(ReservationStation[i].used==false)
                        {
                            ReservationStation[i]=node;
                            ReservationStation[i].used=true;
                            //ReservationStation[i].tag_d=ARF[node.destination_reg].tag;
                            flag=true;
                            curResSize++;
                            break;
                        }
                    }
                    if(flag)
                    {
                        ReOrderNode RB;
                        RB.busy=true;
                        RB.destination_reg=node.destination_reg;
                        RB.order=node.order;
                        RB.valid=false;
                        RB.cur_PC=node.cur_PC;
                        ROB.push_back(RB);
                        InstructionBuffer.erase(InstructionBuffer.begin(),InstructionBuffer.begin()+1);
                    }

                }
                else if(opCode==10)
                {
                    node.instr=inst;
                    jump=true;
                    node.order=ROB_Order;
                    node.cur_PC=InstructionBuffer[0].second;
                    node.tag1=-1;
                    node.tag2=-1;
                    node.s1=hexA[inst[1]];
                    node.s2=hexA[inst[2]];
                    ROB_Order++;
                    bool flag=false;
                    for(int i=0; i<16; i++)
                    {
                        if(ReservationStation[i].used==false)
                        {
                            ReservationStation[i]=node;
                            ReservationStation[i].used=true;
                            //ReservationStation[i].tag_d=ARF[node.destination_reg].tag;
                            flag=true;
                            curResSize++;
                            break;
                        }
                    }
                    if(flag)
                    {
                        ReOrderNode RB;
                        RB.busy=true;
                        RB.destination_reg=node.destination_reg;
                        RB.order=node.order;
                        RB.valid=false;
                        RB.cur_PC=node.cur_PC;
                        ROB.push_back(RB);
                        InstructionBuffer.erase(InstructionBuffer.begin(),InstructionBuffer.begin()+1);
                    }
                }
                else if(opCode==8 || opCode==9)
                {
                   
                    node.instr=inst;
                    node.order=ROB_Order;
                    ROB_Order++;
                    node.destination_reg=hexA[inst[1]];
                    int r1=hexA[inst[2]];
                    int r2=hexA[inst[3]];
                    
                    if(!ARF[r1].busy)
                    {
                        node.s1=ARF[r1].data;
                        node.tag1=-1;
                    }
                    else
                    {
                        int mappedReg=ARF[r1].tag;
                        if(RRF[mappedReg].valid)
                        {
                            node.s1=RRF[mappedReg].data;
                            node.tag1=-1;
                        }
                        else
                        {
                            node.s1=INF;
                            node.tag1=mappedReg;
                        }

                    }
                    if(opCode==9)
                    {
                        
                        if(!ARF[node.destination_reg].busy)
                        {
                            node.s2=ARF[node.destination_reg].data;
                            node.tag2=-1;
                        }
                        else
                        {

                            int mappedReg=ARF[node.destination_reg].tag;
                            if(RRF[mappedReg].valid)
                            {
                                node.s2=RRF[mappedReg].data;
                                node.tag2=-1;
                            }
                            else
                            {
                                node.s2=INF;
                                node.tag2=mappedReg;
                            }

                        }
                    }
                    else
                    {
                        node.s2=r2;
                        node.tag2=-1;
                    }
                    bool flag=false;
                    if(opCode==8)
                    renameDest(node.destination_reg,ARF,RRF);
                    for(int i=0; i<16; i++)
                    {
                        if(ReservationStation[i].used==false)
                        {
                            ReservationStation[i]=node;
                            ReservationStation[i].used=true;
                            ReservationStation[i].tag_d=ARF[node.destination_reg].tag;
                            if(opCode==8)
                            ReservationStation[i].load=true;
                            else
                            ReservationStation[i].store=true;
                            curResSize++;
                            flag=true;
                            break;
                        }
                    }
                    if(flag)
                    {
                        ReOrderNode RB;
                        RB.busy=true;
                        RB.destination_reg=node.destination_reg;
                        RB.order=node.order;
                        RB.valid=false;
                        if(opCode==8)
                        RB.load=true;
                        else
                        RB.store=true;
                        ROB.push_back(RB);
                        InstructionBuffer.erase(InstructionBuffer.begin(),InstructionBuffer.begin()+1);
                    }
                }
                else
                {

                    node.instr=inst;
                    node.destination_reg=hexA[inst[1]];
                    node.order=ROB_Order;
                    ROB_Order++;
                    int r1=hexA[inst[2]];
                    int r2=hexA[inst[3]];
                    int r3=hexA[inst[1]];
                    if(!ARF[r1].busy)
                    {
                        node.s1=ARF[r1].data;
                        node.tag1=-1;
                    }
                    else
                    {

                        int mappedReg=ARF[r1].tag;
                        if(RRF[mappedReg].valid)
                        {
                            node.s1=RRF[mappedReg].data;
                            node.tag1=-1;
                        }
                        else
                        {
                            node.s1=INF;
                            node.tag1=mappedReg;
                        }

                    }
                    if(!ARF[r2].busy)
                    {
                        node.s2=ARF[r2].data;
                        node.tag2=-1;
                    }
                    else
                    {

                        int mappedReg=ARF[r2].tag;
                        if(RRF[mappedReg].valid)
                        {
                            node.s2=RRF[mappedReg].data;
                            node.tag2=-1;
                        }
                        else
                        {
                            node.s2=INF;
                            node.tag2=mappedReg;
                        }

                    }
                     if(opCode==6)
                    {
                        node.s2=INF;
                        node.tag2=-1;
                    }
                    if(opCode==3)
                    {
                        node.s2=1;
                        node.tag2=-1;
                        if(!ARF[r3].busy)
                        {
                            node.s1=ARF[r2].data;
                            node.tag1=-1;
                        }
                        else
                        {

                            int mappedReg=ARF[r3].tag;
                            if(RRF[mappedReg].valid)
                            {
                                node.s1=RRF[mappedReg].data;
                                node.tag1=-1;
                            }
                            else
                            {
                                node.s1=INF;
                                node.tag1=mappedReg;
                            }

                        }

                    }
                    renameDest(node.destination_reg,ARF,RRF);
                    bool flag=false;
                    for(int i=0; i<16; i++)
                    {
                        if(ReservationStation[i].used==false)
                        {
                            ReservationStation[i]=node;
                            ReservationStation[i].used=true;
                            ReservationStation[i].tag_d=ARF[node.destination_reg].tag;
                            flag=true;
                            curResSize++;
                            break;
                        }
                    }
                    if(flag)
                    {
                        ReOrderNode RB;
                        RB.busy=true;
                        RB.destination_reg=node.destination_reg;
                        RB.order=node.order;
                        RB.valid=false;
                        
                        ROB.push_back(RB);
                        InstructionBuffer.erase(InstructionBuffer.begin(),InstructionBuffer.begin()+1);
                    }
                }
            }
        }
        
       if(InstructionBuffer.size()>0)
        {
            string inst=InstructionBuffer[0].first;
            int opCode=hexA[inst[0]];
          
            //cout<<opCode<<"\n";
            if(curResSize<16)
            {
                ResStationNode node;
                if(opCode==15)
                {
                    
                    node.instr=inst;
                    node.order=ROB_Order;
                    ROB_Order++;
                    node.tag1=-1;
                    node.tag2=-1;
                    bool flag=false;
                    for(int i=0; i<16; i++)
                    {
                        if(ReservationStation[i].used==false)
                        {
                            ReservationStation[i]=node;
                            ReservationStation[i].used=true;
                            curResSize++;
                            flag=true;
                            break;
                        }
                    }
                    if(flag)
                    {
                        ReOrderNode RB;
                        RB.busy=true;
                        
                        RB.order=node.order;
                    
                        RB.valid=false;
                        RB.halt=true;
                        ROB.push_back(RB);
                        InstructionBuffer.erase(InstructionBuffer.begin(),InstructionBuffer.begin()+1);
                    }
                }
                else if(opCode==11)
                {
                    node.instr=inst;
                    node.order=ROB_Order;
                    ROB_Order++;
                    con_jump=true;
                    node.tag2=-1;
                    node.s2=16*hexA[inst[2]]+hexA[inst[3]];
                    if(node.s2>=128)
                    node.s2-=256;
                    node.s1=-1;
                    node.cur_PC=InstructionBuffer[0].second;
                    int r1=hexA[inst[1]];
                    if(!ARF[r1].busy)
                    {
                        node.s1=ARF[r1].data;
                        node.tag1=-1;
                    }
                    else
                    {

                        int mappedReg=ARF[r1].tag;
                        if(RRF[mappedReg].valid)
                        {
                            node.s1=RRF[mappedReg].data;
                            node.tag1=-1;
                        }
                        else
                        {
                            node.s1=INF;
                            node.tag1=mappedReg;
                        }

                    }
                    bool flag=false;
                    for(int i=0; i<16; i++)
                    {
                        if(ReservationStation[i].used==false)
                        {
                            ReservationStation[i]=node;
                            ReservationStation[i].used=true;
                            //ReservationStation[i].tag_d=ARF[node.destination_reg].tag;
                            flag=true;
                            curResSize++;
                            break;
                        }
                    }
                    if(flag)
                    {
                        ReOrderNode RB;
                        RB.busy=true;
                        RB.destination_reg=node.destination_reg;
                        RB.order=node.order;
                        RB.valid=false;
                        RB.cur_PC=node.cur_PC;
                        ROB.push_back(RB);
                        InstructionBuffer.erase(InstructionBuffer.begin(),InstructionBuffer.begin()+1);
                    }

                }
                else if(opCode==10)
                {
                    node.instr=inst;
                    jump=true;
                    node.order=ROB_Order;
                    node.cur_PC=InstructionBuffer[0].second;
                    node.tag1=-1;
                    node.tag2=-1;
                    node.s1=hexA[inst[1]];
                    node.s2=hexA[inst[2]];
                    ROB_Order++;
                    bool flag=false;
                    for(int i=0; i<16; i++)
                    {
                        if(ReservationStation[i].used==false)
                        {
                            ReservationStation[i]=node;
                            ReservationStation[i].used=true;
                            //ReservationStation[i].tag_d=ARF[node.destination_reg].tag;
                            flag=true;
                            curResSize++;
                            break;
                        }
                    }
                    if(flag)
                    {
                        ReOrderNode RB;
                        RB.busy=true;
                        RB.destination_reg=node.destination_reg;
                        RB.order=node.order;
                        RB.valid=false;
                        RB.cur_PC=node.cur_PC;
                        ROB.push_back(RB);
                        InstructionBuffer.erase(InstructionBuffer.begin(),InstructionBuffer.begin()+1);
                    }
                }
                else if(opCode==8 || opCode==9)
                {
                   
                    node.instr=inst;
                    node.order=ROB_Order;
                    ROB_Order++;
                    node.destination_reg=hexA[inst[1]];
                    int r1=hexA[inst[2]];
                    int r2=hexA[inst[3]];
                    
                    if(!ARF[r1].busy)
                    {
                        node.s1=ARF[r1].data;
                        node.tag1=-1;
                    }
                    else
                    {
                        int mappedReg=ARF[r1].tag;
                        if(RRF[mappedReg].valid)
                        {
                            node.s1=RRF[mappedReg].data;
                            node.tag1=-1;
                        }
                        else
                        {
                            node.s1=INF;
                            node.tag1=mappedReg;
                        }

                    }
                    if(opCode==9)
                    {
                        
                        if(!ARF[node.destination_reg].busy)
                        {
                            node.s2=ARF[node.destination_reg].data;
                            node.tag2=-1;
                        }
                        else
                        {

                            int mappedReg=ARF[node.destination_reg].tag;
                            if(RRF[mappedReg].valid)
                            {
                                node.s2=RRF[mappedReg].data;
                                node.tag2=-1;
                            }
                            else
                            {
                                node.s2=INF;
                                node.tag2=mappedReg;
                            }

                        }
                    }
                    else
                    {
                        node.s2=r2;
                        node.tag2=-1;
                    }
                    bool flag=false;
                    if(opCode==8)
                    renameDest(node.destination_reg,ARF,RRF);
                    for(int i=0; i<16; i++)
                    {
                        if(ReservationStation[i].used==false)
                        {
                            ReservationStation[i]=node;
                            ReservationStation[i].used=true;
                            ReservationStation[i].tag_d=ARF[node.destination_reg].tag;
                            if(opCode==8)
                            ReservationStation[i].load=true;
                            else
                            ReservationStation[i].store=true;
                            curResSize++;
                            flag=true;
                            break;
                        }
                    }
                    if(flag)
                    {
                        ReOrderNode RB;
                        RB.busy=true;
                        RB.destination_reg=node.destination_reg;
                        RB.order=node.order;
                        RB.valid=false;
                        if(opCode==8)
                        RB.load=true;
                        else
                        RB.store=true;
                        ROB.push_back(RB);
                        InstructionBuffer.erase(InstructionBuffer.begin(),InstructionBuffer.begin()+1);
                    }
                }
                else
                {

                    node.instr=inst;
                    node.destination_reg=hexA[inst[1]];
                    node.order=ROB_Order;
                    ROB_Order++;
                    int r1=hexA[inst[2]];
                    int r2=hexA[inst[3]];
                    int r3=hexA[inst[1]];
                    if(!ARF[r1].busy)
                    {
                        node.s1=ARF[r1].data;
                        node.tag1=-1;
                    }
                    else
                    {

                        int mappedReg=ARF[r1].tag;
                        if(RRF[mappedReg].valid)
                        {
                            node.s1=RRF[mappedReg].data;
                            node.tag1=-1;
                        }
                        else
                        {
                            node.s1=INF;
                            node.tag1=mappedReg;
                        }

                    }
                    if(!ARF[r2].busy)
                    {
                        node.s2=ARF[r2].data;
                        node.tag2=-1;
                    }
                    else
                    {

                        int mappedReg=ARF[r2].tag;
                        if(RRF[mappedReg].valid)
                        {
                            node.s2=RRF[mappedReg].data;
                            node.tag2=-1;
                        }
                        else
                        {
                            node.s2=INF;
                            node.tag2=mappedReg;
                        }

                    }
                    if(opCode==6)
                    {
                        node.s2=INF;
                        node.tag2=-1;
                    }
                    if(opCode==3)
                    {
                        node.s2=1;
                        node.tag2=-1;
                        if(!ARF[r3].busy)
                        {
                            node.s1=ARF[r2].data;
                            node.tag1=-1;
                        }
                        else
                        {

                            int mappedReg=ARF[r3].tag;
                            if(RRF[mappedReg].valid)
                            {
                                node.s1=RRF[mappedReg].data;
                                node.tag1=-1;
                            }
                            else
                            {
                                node.s1=INF;
                                node.tag1=mappedReg;
                            }

                        }

                    }
                    renameDest(node.destination_reg,ARF,RRF);
                    bool flag=false;
                    for(int i=0; i<16; i++)
                    {
                        if(ReservationStation[i].used==false)
                        {
                            ReservationStation[i]=node;
                            ReservationStation[i].used=true;
                            ReservationStation[i].tag_d=ARF[node.destination_reg].tag;
                            flag=true;
                            curResSize++;
                            break;
                        }
                    }
                    if(flag)
                    {
                        ReOrderNode RB;
                        RB.busy=true;
                        RB.destination_reg=node.destination_reg;
                        RB.order=node.order;
                        RB.valid=false;
                        
                        ROB.push_back(RB);
                        InstructionBuffer.erase(InstructionBuffer.begin(),InstructionBuffer.begin()+1);
                    }
                }
            }
        }
        if(InstructionBuffer.size()<2 && jump==false && con_jump==false && set_jump==false && set_con_jump==false)
        {
            
            InstructionBuffer.push_back(make_pair(InstCache[PC],PC));
            PC++;
            if(InstructionBuffer.size()<2)
            {
                    InstructionBuffer.push_back(make_pair(InstCache[PC],PC));
                    PC++;
            }
        }
        if(set_jump)
        {
            PC=real_PC;
            set_jump=false;
        }
        if(set_con_jump)
        {
            PC=con_real_PC;
            set_con_jump=false;
        }
        
    }
    for(ll i=0; i<6; i++)
        cout<<ARF[i].data<<" ";
    cout<<"\n";
    for(ll i=0;i<6;i++)
        cout<<DataCache[i]<<" ";
    cout<<"\n";
    cout<<cycles<<" "<<instructions;
}