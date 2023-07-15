#!/usr/bin/env python
# coding: utf-8

# In[1]:


import networkx as nx
import matplotlib.pyplot as plt
import random
import time
import math as mt
#from tmgen.models import uniform_tm,spike_tm,modulated_gravity_tm,random_gravity_tm,gravity_tm,exp_tm
import csv
import os
import random


# In[ ]:


class Network:
    def __init__(self,config,topology_file_path,fidelity_experiment_flag,edge_fidelity_range,max_edge_capacity,fidelity_threshold_values):
        self.data_dir = './data/'
        if fidelity_experiment_flag:
            self.fidelity_experiment = True
        else:
            self.fidelity_experiment = False
        self.set_E = []
        self.fidelity_threshold_values = fidelity_threshold_values
        self.max_edge_capacity_value = max_edge_capacity
        self.edge_fidelity_range = edge_fidelity_range
        self.each_edge_capacity = {(1,2):20,(2,3):20,(3,4):20,(4,5):20,(2,7):20,(7,8):20,(8,9):20,
                                   (9,5):20,(5,6):20,(2,10):20,(10,11):20,(11,12):20,(12,5):20}
        
        self.max_edge_capacity = 10
        #self.topology_file = data_dir + config.topology_file
        self.topology_file = topology_file_path
        
        #self.DG = nx.DiGraph()
        self.set_E = []
        self.each_id_pair ={}
        self.pair_id = 0
        self.max_edge_capacity = int(config.max_edge_capacity)
        self.min_edge_capacity = int(config.min_edge_capacity)
        self.min_edge_fidelity = float(config.min_edge_fidelity)
        self.max_edge_fidelity = float(config.max_edge_fidelity)
        self.fidelity_threshold_range = 0.0
        self.num_of_paths = int(config.num_of_paths)
        self.path_selection_scheme = config.path_selection_scheme
        self.delat_value = int(config.delat_value)
        self.storage_capacity = int(config.storage_capacity)
        self.T = []
        self.path_existance_flag = False
        self.storages = []
        self.each_pair_id  ={}
        
        for i in range(int(config.time_intervals)):
            self.T.append(i)
        self.each_request_threshold = {}
        self.set_of_paths = {}
        self.each_request_real_paths = {}
        self.each_request_virtual_paths = {}
        self.each_n_f_purification_result = {}
        self.storage_pairs = [(2,5),(10,12)]
        
        self.each_storage_capacity = {2:1000,5:1000,10:1000,12:1000}
        self.each_storage_capacity = {}
        self.storage_pairs = []
        self.storage_nodes = []
        self.each_edge_target_fidelity = {}
        self.each_user_pair_all_real_paths = {}
        self.each_user_pair_all_real_disjoint_paths = {}
        self.each_user_pair_real_paths = {}
        self.each_user_pair_virtual_paths = {}
        self.nodes = []
        self.oracle_for_target_fidelity = {}
        self.storage_node_pairs = []
        self.each_t_user_pairs = {}
        self.each_storage_real_paths = {}
        self.each_request_virtual_paths_include_subpath = {}
        self.each_path_path_id = {}
        self.global_each_basic_fidelity_target_fidelity_required_EPRs = {}
        self.all_basic_fidelity_target_thresholds = []
        self.path_counter_id = 0
        self.pair_id = 0
        self.each_user_each_t_weight={}
        self.each_path_legth = {}
        
        
        self.load_topology()
    
    def load_topology(self):
       
        self.set_E=[]
        self.each_edge_capacity={}
        self.nodes = []
        self.each_edge_fidelity = {}
        self.link_idx_to_sd = {}
        self.link_sd_to_idx = {}
        
        self.g = nx.Graph()
        print('[*] Loading topology...', self.topology_file)
        f = open(self.topology_file, 'r')
        
        header = f.readline()
        #print("this is header ",header)

        for line in f:
            line = line.strip()
            link = line.split('\t')
            #print(line,link)
            i, s, d,  c = link
            if int(s) not in self.nodes:
                self.nodes.append(int(s))
            if int(d) not in self.nodes:
                self.nodes.append(int(d))
            self.set_E.append((int(s),int(d)))
            random_fidelity = random.uniform(self.min_edge_fidelity,self.max_edge_fidelity)
            self.each_edge_fidelity[(int(s),int(d))] = round(random_fidelity,3)
            self.each_edge_fidelity[(int(d),int(s))] = round(random_fidelity,3)

            edge_capacity = random.randint(self.min_edge_capacity, self.max_edge_capacity)

            
            self.each_edge_capacity[(int(s),int(d))] = edge_capacity
            
            self.g.add_edge(int(s),int(d),weight=1)
            self.g.add_edge(int(d),int(s),weight=1)
        
        f.close()
        
        
        
    def get_next_fidelity_and_succ_prob(self,F):
        succ_prob = (F+((1-F)/3))**2 + (2*(1-F)/3)**2
        output_fidelity = (F**2 + ((1-F)/3)**2)/succ_prob

        return output_fidelity, succ_prob

    def get_avg_epr_pairs(self,F_init,F_target):
        F_curr = F_init
        n_avg = 1.0
        while(F_curr < F_target):
            F_curr,succ_prob = self.get_next_fidelity_and_succ_prob(F_curr)
            n_avg = n_avg*(2/succ_prob)
        return  n_avg

    def get_avg_output_fidelity(self,F_init,n_avg):
        F_curr = F_init
        n_curr = 1
        while(1):
            F_prev,succ_prob = self.get_next_fidelity_and_succ_prob(F_curr)
            n_curr = n_curr*(2/succ_prob)

            if(n_curr > n_avg):
                break
            else:
                F_curr = F_prev

        return F_curr
    def recursive_purification(self,n,f):
        #print("n is ",n)
        n = int(n)
        if f ==1.0:
            return f
        else:
            if n<=0 or (n==1):
                return f
            else:
                numerator=  f * self.recursive_purification(n-1,f)
                denominator = numerator + (1-f) * (1-self.recursive_purification(n-1,f))

                return round(numerator/(denominator),4)
    
    def get_possible_threshold_for_each_n(self,basic_fidelities):
    #         for path in self.set_of_paths:
    #             for f in [0.6,0.7,0.8,0.9,1.0]:
    #                 try:
    #                     self.oracle_for_target_fidelity[path][f] = 4
    #                 except:
    #                     self.oracle_for_target_fidelity[path] = {}
    #                     self.oracle_for_target_fidelity[path][f] = 4
        n_values = []
        each_basic_fidelity_each_EPR_number_target_fidelity = {}

        for f in basic_fidelities:
            n = 1
            each_basic_fidelity_each_EPR_number_target_fidelity[f] = {}
            final_fidelity = f
            if n not in n_values:
                n_values.append(n)
            each_basic_fidelity_each_EPR_number_target_fidelity[f][n] = final_fidelity
            #print("for basic fidelity ",str(f))
            while n <20:
                n+=1
                if n not in n_values:
                    n_values.append(n)
                final_fidelity = self.recursive_purification(n,f)
                each_basic_fidelity_each_EPR_number_target_fidelity[f][n] = final_fidelity
            #print("for basic fidelity ",str(f),"we are done!")
        return each_basic_fidelity_each_EPR_number_target_fidelity,n_values
    
    def get_next_fidelity_and_succ_prob_BBPSSW(self,F):
        succ_prob = (F+((1-F)/3))**2 + (2*(1-F)/3)**2
        output_fidelity = (F**2 + ((1-F)/3)**2)/succ_prob

        return output_fidelity, succ_prob

    def get_next_fidelity_and_succ_prob_DEJMPS(self,F1,F2,F3,F4):
        succ_prob = (F1+F2)**2 + (F3+F4)**2
        output_fidelity1 = (F1**2 + F2**2)/succ_prob
        output_fidelity2 = (2*F3*F4)/succ_prob
        output_fidelity3 = (F3**2 + F4**2)/succ_prob
        output_fidelity4 = (2*F1*F2)/succ_prob

        return output_fidelity1, output_fidelity2, output_fidelity3, output_fidelity4, succ_prob

    def get_avg_epr_pairs_BBPSSW(self,F_init,F_target):
        F_curr = F_init
        n_avg = 1.0
        while(F_curr < F_target):
            F_curr,succ_prob = get_next_fidelity_and_succ_prob_BBPSSW(F_curr)
            n_avg = n_avg*(2/succ_prob)
        return  n_avg

    def get_avg_epr_pairs_DEJMPS(self,F_init,F_target):
        F_curr = F_init
        F2 = F3 = F4 = (1-F_curr)/3
        n_avg = 1.0
        while(F_curr < F_target):
            F_curr,F2, F3, F4, succ_prob = self.get_next_fidelity_and_succ_prob_DEJMPS(F_curr, F2, F3, F4)
            n_avg = n_avg*(2/succ_prob)
        return  n_avg
    
    


  

    
    def reset_pair_paths(self):
        self.set_of_paths = {}
        self.each_user_pair_all_real_paths = {}
        self.each_user_pair_all_real_disjoint_paths = {}
        self.each_request_real_paths = {}
        self.each_request_virtual_paths = {}
        self.each_request_virtual_paths_include_subpath = {}
        self.each_path_path_id = {}
        self.each_storage_real_paths = {}    
        self.path_existance_flag = False
    def check_demands_per_each_time(self,each_t_user_pairs):
        for time in self.T:
            for user_pair in each_t_user_pairs[time]:
                if self.each_t_each_request_demand[time][user_pair]==0:
                    self.each_t_each_request_demand[time][user_pair] = 1.0
    def set_each_user_pair_demands(self,number_of_time_slots,each_t_user_pairs,spike_mean,num_spikes):
        self.each_t_each_request_demand = {}
        num_of_pairs= len(list(each_t_user_pairs[0]))
#         print(num_of_pairs,num_spikes,spike_mean,number_of_time_slots)
#         print("each_t_user_pairs",each_t_user_pairs)
        tm = spike_tm(num_of_pairs+1,num_spikes,spike_mean,number_of_time_slots)
        for time in self.T:
            traffic = tm.at_time(time)
            printed_pairs = []
            user_indx = 0
            for i in range(num_of_pairs):
                for j in range(num_of_pairs):
                    if i!=j:
                        if (i,j) not in printed_pairs and (j,i) not in printed_pairs and user_indx<num_of_pairs:
                            printed_pairs.append((i,j))
                            printed_pairs.append((j,i))
#                             print("num_of_pairs %s time %s traffic from %s to %s is %s and user_indx %s"%(num_of_pairs, time,i,j,traffic[i][j],user_indx))
                            request = each_t_user_pairs[time][user_indx]
                            user_indx+=1
                            demand = max(1,traffic[i][j])
                            try:
                                self.each_t_each_request_demand[time][request] = demand
                            except:
                                self.each_t_each_request_demand[time] = {}
                                self.each_t_each_request_demand[time][request] = demand
                                

                
        for request in each_t_user_pairs[time]:
            try:
                self.each_t_each_request_demand[0][request] = 0
            except:
                self.each_t_each_request_demand[0]={}
                self.each_t_each_request_demand[0][request] = 0
    def set_each_user_pair_demands_randomly(self,number_of_time_slots,each_t_user_pairs,spike_mean,num_spikes):
        
        self.each_t_each_request_demand = {}
        num_of_pairs= len(list(each_t_user_pairs[0]))
#         print(num_of_pairs,num_spikes,spike_mean,number_of_time_slots)
#         print("each_t_user_pairs",each_t_user_pairs)
        
        for time in self.T:
            printed_pairs = []
            user_indx = 0
            for i in range(num_of_pairs):
                for j in range(num_of_pairs):
                    if i!=j:
                        if (i,j) not in printed_pairs and (j,i) not in printed_pairs and user_indx<num_of_pairs:
                            printed_pairs.append((i,j))
                            printed_pairs.append((j,i))
#                             print("num_of_pairs %s time %s traffic from %s to %s is %s and user_indx %s"%(num_of_pairs, time,i,j,traffic[i][j],user_indx))
                            request = each_t_user_pairs[time][user_indx]
                            user_indx+=1
                            demand = random.randint(0,10)
                            try:
                                self.each_t_each_request_demand[time][request] = demand
                            except:
                                self.each_t_each_request_demand[time] = {}
                                self.each_t_each_request_demand[time][request] = demand
                                

                
        for request in each_t_user_pairs[time]:
            try:
                self.each_t_each_request_demand[0][request] = 0
            except:
                self.each_t_each_request_demand[0]={}
                self.each_t_each_request_demand[0][request] = 0
    def get_each_request_threshold(self,k,t):
        return self.each_request_threshold[k][t]
    def set_each_user_weight_over_time(self):
#          for t,user_weight in self.each_work_load_each_t_user_weight[wk_idx].items():
#             for k,weight in user_weight.items():
#                 k_id = self.each_pair_id[k]
        for time,user_pairs in self.each_t_user_pairs.items():
            #print("for time ",time)
            for user in user_pairs:
                user_pair = self.each_id_pair[user]
                #print("for user pair %s with id %s"%(user_pair,user))
                #print("getting weight from loaded from file for wk %s time %s user pair %s"%(wk_idx,time,user_pair))
                #print(self.each_work_load_each_t_user_weight[wk_idx].keys())
                weight = self.each_work_load_each_t_user_weight[wk_idx+time][(user_pair)]
                #print("weight is ",weight)
                try:
                    self.each_user_each_t_weight[user][time] = weight
                except:
                    self.each_user_each_t_weight[user]= {}
                    self.each_user_each_t_weight[user][time] = weight
        import pdb
        #pdb.set_trace()
    def reset_variables(self):
        self.each_t_requests = {}
        self.each_t_real_requests = {}
        self.set_of_paths = {}
        self.each_user_pair_all_real_paths = {}
        self.each_user_pair_all_real_disjoint_paths = {}
        self.each_request_real_paths = {}
        self.each_request_virtual_paths = {}
        self.each_request_virtual_paths2 = {}
        self.each_request_virtual_paths_include_subpath = {}
        self.each_user_path_path_id = {}
        self.each_storage_path_path_id = {}
        self.each_storage_real_paths = {}
        self.set_of_paths = {}
        self.each_request_real_paths = {}
        self.each_request_virtual_paths = {}
        self.each_n_f_purification_result = {}
        self.each_storage_capacity = {}
        self.storage_pairs = []
        self.storage_nodes = []
        self.storage_node_pairs = []
        self.each_user_pair_all_real_paths = {}
        self.each_user_pair_all_real_disjoint_paths = {}
        self.each_user_pair_real_paths = {}
        self.each_user_pair_virtual_paths = {}
        self.each_request_virtual_paths2 = {}
        self.each_storage_real_paths = {}
        self.each_request_virtual_paths_include_subpath = {}
        self.each_path_path_id = {}
        self.global_each_basic_fidelity_target_fidelity_required_EPRs = {}
        self.all_basic_fidelity_target_thresholds = []
        self.path_counter_id = 0
        self.each_user_each_t_weight={}
        
    def set_each_time_requests(self):
        self.each_t_requests = {}
        for t,user_pairs in self.each_t_user_pairs.items():
            for pair in user_pairs:
                try:
                    if pair not in self.each_t_requests[t]:
                        try:
                            self.each_t_requests[t].append(pair)
                        except:
                            self.each_t_requests[t] = [pair]
                except:
                    self.each_t_requests[t] = [pair]
            for pair in self.storage_pairs:
                try:
                    if pair not in self.each_t_requests[t]:
                        try:
                            self.each_t_requests[t].append(pair)
                        except:
                            self.each_t_requests[t] = [pair]
                except:
                    self.each_t_requests[t] = [pair]
    def set_each_time_real_requests(self,each_t_user_pairs):
        self.each_t_real_requests = {}
        for t,user_pairs in each_t_user_pairs.items():
            for pair in user_pairs:
                try:
                    if pair not in self.each_t_real_requests[t]:
                        try:
                            self.each_t_real_requests[t].append(pair)
                        except:
                            self.each_t_real_requests[t] = [pair]
                except:
                    self.each_t_real_requests[t] = [pair]
    def set_storage_pairs_as_user_pairs(self, storage_pairs):
        for time in self.T:
            for pair in storage_pairs:
#                 try:
#                     if pair not in self.each_t_requests[time]:
#                         self.each_t_requests[time].append(pair)
#                 except:
#                     self.each_t_requests[time] =[pair]
                try:
                    self.each_t_each_request_demand[time][pair] = 0
                except:
                    self.each_t_each_request_demand[time] = {}
                    self.each_t_each_request_demand[time][pair] = 0
   
    def set_paths_in_the_network(self):
        
        self.reset_pair_paths()
        self.each_request_real_paths = {}
        """with new storage pairs, we will check the solution for each number of paths(real and virtual)"""
        #print("self.each_t_user_pairs ",self.each_t_user_pairs)
        pairs = []
        for t,user_pairs in self.each_t_user_pairs.items():            
            for user_pair in user_pairs:
                if user_pair not in pairs:
                    pairs.append(user_pair)
        self.get_each_user_pair_real_paths(pairs)
        self.set_each_time_requests()
        self.set_each_time_real_requests(self.each_t_user_pairs)
        self.get_each_user_pair_real_paths(self.storage_pairs)
        self.set_real_paths(self.storage_pairs,pairs)
        #print("storages real paths ",self.each_storage_real_paths)
        self.set_virtual_paths(pairs)
        #import pdb
        #pdb.set_trace()
        self.set_storage_pairs_as_user_pairs(self.storage_pairs)
        self.set_each_path_basic_fidelity()
        
        """we set the required EPR pairs to achieve each request threshold fidelity"""
        #network.set_required_EPR_pairs_for_path_fidelity_threshold()
        #print("self.each_t_requests ",self.each_t_requests)
        #print("self.each_t_real_requests ",self.each_t_real_requests)
        #self.check_each_request_real_virtual_paths()
        self.set_required_EPR_pairs_for_each_path_each_fidelity_threshold()
        
        
      
    def load_testing_topology(self):
       
        self.set_E=[]
        self.each_edge_capacity={}
        self.nodes = []
        self.max_edge_capacity = 0
        self.g = nx.Graph()
        print('[*] Loading topology...', self.topology_file)
        f = open(self.topology_file, 'r')
        header = f.readline()
#         f.readline()
#         self.link_capacities = np.empty((self.num_links))
#         self.link_weights = np.empty((self.num_links))
        for line in f:
            line = line.strip()
            link = line.split('\t')
#             print(line,link)
            i, s, d, c = link
            if int(s) not in self.nodes:
                self.nodes.append(int(s))
            if int(d) not in self.nodes:
                self.nodes.append(int(d))
            
            self.set_E.append((int(s),int(d)))
            random_capacity = random.randint(200, 400)
            
            if (int(s),int(d)) ==(1,2) or (int(s),int(d))== (4,5) or (int(s),int(d)) == (2,1) or (int(s),int(d)) == (5,4):
                random_capacity = 100
            else:
                random_capacity = 10
#             print("for edge ",(int(s),int(d)),"capacity is ",random_capacity)
            self.each_edge_capacity[(int(s),int(d))] = random_capacity
            if random_capacity>self.max_edge_capacity:
                self.max_edge_capacity  = random_capacity
            self.g.add_edge(int(s),int(d),weight=1)
#             self.link_capacities[int(i)] = float(c)
#             self.link_weights[int(i)] = int(w)
#             self.DG.add_weighted_edges_from([(int(s),int(d),int(w))])
#             self.set_E.append()
        
        f.close()  
        
    def get_user_pairs_over_dynamicly_chaning_population(self,number_of_user_pairs,distance_between_users,number_of_time_slots):
        self.each_t_user_pairs = {}
        candidate_user_pairs = []

        for src in self.nodes:
            for dst in self.nodes:
                if src!=dst and (src,dst) not in self.set_E and (dst,src) not in self.set_E:
                    shortest_path = nx.shortest_path(self.g, source=src, target=dst)
#                     if len(shortest_path)>=distance_between_users:
                    if (src,dst) not in candidate_user_pairs and (dst,src) not in candidate_user_pairs:
                        candidate_user_pairs.append((src,dst))
        #print("these are candidate pairs",candidate_user_pairs)
        #candidate_user_pairs = [(1,6),(2,10),(4,8),(6,11),(5,10),(3,9),(8,10),(0,3),(1,10),(2,5)]
        for t in range(number_of_time_slots):
            self.each_t_user_pairs[t] = []
        selected_user_pairs = []
        while(len(candidate_user_pairs)<number_of_time_slots *number_of_user_pairs):
            number_of_user_pairs =number_of_user_pairs-1
            
        for t in range(number_of_time_slots):
            while(len(self.each_t_user_pairs[t])<number_of_user_pairs):
                user_pair = candidate_user_pairs[random.randint(0,len(candidate_user_pairs)-1)]
                if user_pair not in self.each_t_user_pairs[t] and user_pair not in selected_user_pairs:
                    selected_user_pairs.append(user_pair)
                    try:
                        self.each_t_user_pairs[t].append(user_pair)
                    except:
                        self.each_t_user_pairs[t]=[user_pair]
    def get_testing_user_pairs(self,number_of_user_pairs,distance,number_of_time_slots):
        self.each_t_user_pairs = {}
        candidate_user_pairs = []
        for src in self.nodes:
            for dst in self.nodes:
                if src!=dst and (src,dst) not in self.set_E and (dst,src) not in self.set_E:
                    shortest_path = nx.shortest_path(self.g, source=src, target=dst)
                    if len(shortest_path)>=distance:
                        if (src,dst) not in candidate_user_pairs and (dst,src) not in candidate_user_pairs:
                            candidate_user_pairs.append((src,dst))
        candidate_user_pairs.append((1,5))
        #print("these are candidate pairs",candidate_user_pairs)
        #candidate_user_pairs = [(1,6),(2,10),(4,8),(6,11),(5,10),(3,9),(8,10),(0,3),(1,10),(2,5)]
        for t in range(number_of_time_slots):
            self.each_t_user_pairs[t] = []
        selected_fixed_user_pairs = []
        while(len(selected_fixed_user_pairs)<number_of_user_pairs):
            user_pair = candidate_user_pairs[random.randint(0,len(candidate_user_pairs)-1)]
            if user_pair not in selected_fixed_user_pairs:
                selected_fixed_user_pairs.append(user_pair)
        for t in range(number_of_time_slots):
            try:
                self.each_t_user_pairs[t]= [(1,5)]
            except:
                self.each_t_user_pairs[t]= [(1,5)]
    def get_user_pairs_online(self,number_of_user_pairs,distance_between_users,number_of_time_slots):
        each_t_user_pairs = {0: [(19, 24), (0, 18), (11, 23)], 
                     1: [(19, 24), (0, 18), (11, 23)], 
                     2: [(19, 24), (0, 18), (11, 23)], 
                     3: [(19, 24), (0, 18), (11, 23)], 
                     4: [(19, 24), (0, 18), (11, 23)], 
                     5: [(19, 24), (0, 18), (11, 23)], 
                     6: [(19, 24), (0, 18), (11, 23)], 
                     7: [(19, 24), (0, 18), (11, 23)], 
                     8: [(19, 24), (0, 18), (11, 23)], 
                     9: [(19, 24), (0, 18), (11, 23)], 
                     10: [(19, 24), (0, 18), (11, 23)], 
                     11: [(19, 24), (0, 18), (11, 23)], 
                     12: [(19, 24), (0, 18), (11, 23)], 
                     13: [(19, 24), (0, 18), (11, 23)], 
                     14: [(19, 24), (0, 18), (11, 23)]}
        for t,user_pairs in each_t_user_pairs.items():
            self.each_t_user_pairs[t]= user_pairs
        
    def get_user_pairs(self,number_of_user_pairs,distance,number_of_time_slots):
        self.each_t_user_pairs = {}
        self.pair_id = 0
        self.each_id_pair ={}
        self.each_pair_id={}
        candidate_user_pairs = []
        self.each_t_requests = {}
        self.each_t_real_requests = {}
        while(len(candidate_user_pairs)<number_of_user_pairs):
            for src in self.nodes:
                for dst in self.nodes:
                    if src!=dst and (src,dst) not in self.set_E and (dst,src) not in self.set_E:
                        #shortest_path = nx.shortest_path(self.g, source=src, target=dst)
                        #if len(shortest_path)>=distance:
                        if (src,dst) not in candidate_user_pairs and (dst,src) not in candidate_user_pairs:
                            candidate_user_pairs.append((src,dst))
        for t in range(number_of_time_slots):
            self.each_t_user_pairs[t] = []
        selected_fixed_user_pairs = []
        while(len(selected_fixed_user_pairs)<number_of_user_pairs):
            user_pair = candidate_user_pairs[random.randint(0,len(candidate_user_pairs)-1)]
            if user_pair not in selected_fixed_user_pairs:
                selected_fixed_user_pairs.append(user_pair)
        selected_ids = []
        #print("selected_fixed_user_pairs",selected_fixed_user_pairs)
        for pair in selected_fixed_user_pairs:
            self.each_id_pair[self.pair_id] = pair
            self.each_pair_id[pair] = self.pair_id
            selected_ids.append(self.pair_id)
            self.pair_id+=1
        for t in range(number_of_time_slots):
            try:
                self.each_t_user_pairs[t]= selected_ids
            except:
                self.each_t_user_pairs[t]= selected_ids

                    
    def set_each_request_fidelity_threshold(self):
        self.each_user_request_fidelity_threshold = {}
        possible_thresholds_based_on_given_range = []
        
        possible_thresholds_based_on_given_range.append(self.fidelity_threshold_range)
#         for t,user_pairs in self.each_t_user_pairs.items():
#             for pair in user_pairs:
#                 self.each_user_request_fidelity_threshold[pair] = possible_thresholds_based_on_given_range[random.randint(0,len(possible_thresholds_based_on_given_range)-1)]
        for time,pairs in self.each_t_user_pairs.items():
            for pair in pairs:
                try:
                    self.each_request_threshold[pair][time]= possible_thresholds_based_on_given_range[random.randint(0,len(possible_thresholds_based_on_given_range)-1)]
                except:
                    self.each_request_threshold[pair] = {}
                    self.each_request_threshold[pair][time] = possible_thresholds_based_on_given_range[random.randint(0,len(possible_thresholds_based_on_given_range)-1)]
                
   
#         print("this is each request each t threshold ",self.each_request_threshold)
#         print("self.each_t_user_pairs",self.each_t_user_pairs)
        
    def set_each_storage_fidelity_threshold(self):
        for pair in self.storage_pairs:
            for time in self.T:
                try:
                    self.each_request_threshold[pair][time] = 0.6
                except:
                    self.each_request_threshold[pair]= {}
                    self.each_request_threshold[pair][time] = 0.6
#         print("this is each storage request each t threshold ",self.each_request_threshold)
    def set_each_path_length(self,path_id,path):
        self.each_path_legth[path_id] = len(path)
    
    def check_if_request_uses_this_sub_path(self,k,p,p_s):
        if p in self.each_request_virtual_paths_include_subpath[k][p_s]:
            return True
        else:
            return False
        
    def remove_storage_pair_real_path_from_path(self,sub_path,path):
        A = path
        B = sub_path
        start_ind = None
        for i in range(len(A)):
            if A[i:i+len(B)] == B:
                start_ind = i
                break

        C = [x for i, x in enumerate(A) 
             if start_ind is None or not(start_ind <= i < (start_ind + len(B)))]
            
        return C
    def get_next_fidelity_and_succ_prob(self,F):
        succ_prob = (F+((1-F)/3))**2 + (2*(1-F)/3)**2
        output_fidelity = (F**2 + ((1-F)/3)**2)/succ_prob

        return output_fidelity, succ_prob

    def get_avg_epr_pairs(self,F_init,F_target):
        F_curr = F_init
        n_avg = 1.0
        while(F_curr < F_target):
            F_curr,succ_prob = self.get_next_fidelity_and_succ_prob(F_curr)
            n_avg = n_avg*(2/succ_prob)
        return  n_avg

    def get_avg_output_fidelity(self,F_init,n_avg):
        F_curr = F_init
        n_curr = 1
        while(1):
            F_prev,succ_prob = self.get_next_fidelity_and_succ_prob(F_curr)
            n_curr = n_curr*(2/succ_prob)

            if(n_curr > n_avg):
                break
            else:
                F_curr = F_prev

        return F_curr
    def recursive_purification(self,n,f):
        #print("n is ",n)
        n = int(n)
        if f ==1.0:
            return f
        else:
            if n<=0 or (n==1):
                return f
            else:
                numerator=  f * self.recursive_purification(n-1,f)
                denominator = numerator + (1-f) * (1-self.recursive_purification(n-1,f))

                return round(numerator/(denominator),4)
    
    def get_possible_threshold_for_each_n(self,basic_fidelities):
        n_values = []
        each_basic_fidelity_each_EPR_number_target_fidelity = {}

        for f in basic_fidelities:
            n = 1
            each_basic_fidelity_each_EPR_number_target_fidelity[f] = {}
            final_fidelity = f
            if n not in n_values:
                n_values.append(n)
            each_basic_fidelity_each_EPR_number_target_fidelity[f][n] = final_fidelity
            #print("for basic fidelity ",str(f))
            while n <20:
                n+=1
                if n not in n_values:
                    n_values.append(n)
                final_fidelity = self.recursive_purification(n,f)
                each_basic_fidelity_each_EPR_number_target_fidelity[f][n] = final_fidelity
            #print("for basic fidelity ",str(f),"we are done!")
        return each_basic_fidelity_each_EPR_number_target_fidelity,n_values
    
    def get_next_fidelity_and_succ_prob_BBPSSW(self,F):
        succ_prob = (F+((1-F)/3))**2 + (2*(1-F)/3)**2
        output_fidelity = (F**2 + ((1-F)/3)**2)/succ_prob

        return output_fidelity, succ_prob

    def get_next_fidelity_and_succ_prob_DEJMPS(self,F1,F2,F3,F4):
        succ_prob = (F1+F2)**2 + (F3+F4)**2
        output_fidelity1 = (F1**2 + F2**2)/succ_prob
        output_fidelity2 = (2*F3*F4)/succ_prob
        output_fidelity3 = (F3**2 + F4**2)/succ_prob
        output_fidelity4 = (2*F1*F2)/succ_prob

        return output_fidelity1, output_fidelity2, output_fidelity3, output_fidelity4, succ_prob

    def get_avg_epr_pairs_BBPSSW(self,F_init,F_target):
        F_curr = F_init
        n_avg = 1.0
        while(F_curr < F_target):
            F_curr,succ_prob = get_next_fidelity_and_succ_prob_BBPSSW(F_curr)
            n_avg = n_avg*(2/succ_prob)
        return  n_avg

    def get_avg_epr_pairs_DEJMPS(self,F_init,F_target):
        F_curr = F_init
        F2 = F3 = F4 = (1-F_curr)/3
        n_avg = 1.0
        while(F_curr < F_target):
            F_curr,F2, F3, F4, succ_prob = self.get_next_fidelity_and_succ_prob_DEJMPS(F_curr, F2, F3, F4)
            n_avg = n_avg*(2/succ_prob)
        return  n_avg
    
    
    def set_required_EPR_pairs_for_each_path_each_fidelity_threshold(self):
        targets = []
        for t in self.fidelity_threshold_values:
            targets.append(t)
        targets.append(0.6)
        targets.sort()
        for path,path_basic_fidelity in self.each_path_basic_fidelity.items():
            #print("for path %s with lenght %s fidelity %s"%(path,self.each_path_legth[path],path_basic_fidelity))
            try:
                if path_basic_fidelity in self.global_each_basic_fidelity_target_fidelity_required_EPRs:
                    
                    for target in targets:
                        
                        #print("getting required rounds for initial F %s to target %s path length %s"%(path_basic_fidelity,target,self.each_path_legth[path]))
                        n_avg = self.global_each_basic_fidelity_target_fidelity_required_EPRs[path_basic_fidelity][target]
                        #print("we got ",n_avg)
                        try:
                            self.oracle_for_target_fidelity[path][target] = n_avg
                            
                        except:
                            self.oracle_for_target_fidelity[path] = {}
                            self.oracle_for_target_fidelity[path][target] = n_avg
                            
                else:
                    
                    for target in targets:
                        
                        #print("getting required rounds for initial F %s to target %s path lenght %s "%(path_basic_fidelity,target,self.each_path_legth[path]))
                        n_avg = self.get_avg_epr_pairs(path_basic_fidelity ,target)
                        n_avg = self.get_avg_epr_pairs_DEJMPS(path_basic_fidelity ,target)
                        #print("we got ",n_avg)
                        try:
                            self.global_each_basic_fidelity_target_fidelity_required_EPRs[path_basic_fidelity][target] =n_avg 
                        except:
                            self.global_each_basic_fidelity_target_fidelity_required_EPRs[path_basic_fidelity]={}
                            self.global_each_basic_fidelity_target_fidelity_required_EPRs[path_basic_fidelity][target] =n_avg 
                            
                        try:
                            self.oracle_for_target_fidelity[path][target] = n_avg
                            
                        except:
                            self.oracle_for_target_fidelity[path] = {}
                            self.oracle_for_target_fidelity[path][target] = n_avg
                            
            except:
                
                for target in targets:
                    n_avg = self.get_avg_epr_pairs(path_basic_fidelity ,target)
                    try:
                        self.global_each_basic_fidelity_target_fidelity_required_EPRs[path_basic_fidelity][target] =n_avg 
                    except:
                        self.global_each_basic_fidelity_target_fidelity_required_EPRs[path_basic_fidelity]={}
                        self.global_each_basic_fidelity_target_fidelity_required_EPRs[path_basic_fidelity][target] =n_avg                     
                    try:
                        self.oracle_for_target_fidelity[path][target] = n_avg
                        
                    except:
                        self.oracle_for_target_fidelity[path] = {}
                        self.oracle_for_target_fidelity[path][target] = n_avg
                        
#         print("self.self.oracle_for_target_fidelity",self.oracle_for_target_fidelity)
    def set_required_EPR_pairs_for_path_fidelity_threshold(self):
        targets = []
        for t in self.fidelity_threshold_values:
            targets.append(t)
        targets.append(0.6)
        targets.sort()
        basic_fidelities = []
        for path,basic_fidelity in self.each_path_basic_fidelity.items():
            if basic_fidelity not in self.all_basic_fidelity_target_thresholds:
                self.all_basic_fidelity_target_thresholds.append(basic_fidelity)
                if basic_fidelity not in basic_fidelities:
                    basic_fidelities.append(basic_fidelity)
                    
        if basic_fidelities:
#             print("we are going to get required EPRs to each thresholds for basics",basic_fidelities)
#             time.sleep(10)
            each_basic_fidelity_each_EPR_number_target_fidelity , n_values=self.get_possible_threshold_for_each_n(basic_fidelities)
            each_basic_fidelity_target_fidelity_required_EPRs = {}
            each_basic_available_targets= {}
            for basic_fidelity,n_final_fidelity in each_basic_fidelity_each_EPR_number_target_fidelity.items():
                each_basic_fidelity_target_fidelity_required_EPRs[basic_fidelity] = {}
                each_basic_available_targets[basic_fidelity] = {}
                available_targets = []
                for n,final_fidelity in n_final_fidelity.items():
            #         print("with basic %s to reach %s you need %s"%(basic_fidelity,final_fidelity,n))
                    if final_fidelity<=0.6:
                        target_fidelity_threshold = 0.6
                    elif final_fidelity<=0.65:
                        target_fidelity_threshold = 0.65
                    elif final_fidelity<=0.7:
                        target_fidelity_threshold = 0.7
                    elif final_fidelity<=0.75:
                        target_fidelity_threshold = 0.75
                    elif final_fidelity<=0.8:
                        target_fidelity_threshold = 0.8
                    elif final_fidelity<=0.85:
                        target_fidelity_threshold = 0.85
                    elif final_fidelity<=0.9:
                        target_fidelity_threshold = 0.9
                    elif final_fidelity<=0.95:
                        target_fidelity_threshold = 0.95 
                    elif final_fidelity<=0.98:
                        target_fidelity_threshold = 0.98
                    elif final_fidelity<=1:
                        target_fidelity_threshold = 1
            #         print("for basic fidelity %s with %s you will get %s "%(basic_fidelity,n,final_fidelity))
                    if target_fidelity_threshold not in available_targets:
                        available_targets.append(target_fidelity_threshold)
                    try:
                        each_basic_fidelity_target_fidelity_required_EPRs[basic_fidelity][target_fidelity_threshold].append(n)
                    except:
                        each_basic_fidelity_target_fidelity_required_EPRs[basic_fidelity][target_fidelity_threshold]=[n]
    #             print("available_targets        ",available_targets)
    #             print("targets                  ",targets)

                each_basic_available_targets[basic_fidelity] = available_targets
                targets.sort()
                for target in targets:
                    if target <= basic_fidelity:
                        each_basic_fidelity_target_fidelity_required_EPRs[basic_fidelity][target]=[1]
                        try:
                            if target not in each_basic_available_targets[basic_fidelity]:
                                each_basic_available_targets[basic_fidelity].append(target)
                        except:
                            each_basic_available_targets[basic_fidelity]=[target]
                for target in targets:
            #         print("with basic %s for target %s"%(basic_fidelity,target))
                    if target in available_targets:
                        last_target_threshold_n = min(each_basic_fidelity_target_fidelity_required_EPRs[basic_fidelity][target])+1
                        last_available_target_threshold = target
                    if target not in available_targets:
                        try:
                            each_basic_fidelity_target_fidelity_required_EPRs[basic_fidelity][target].append(last_target_threshold_n)
                        except:
                            each_basic_fidelity_target_fidelity_required_EPRs[basic_fidelity][target]=[last_target_threshold_n]



            for basic in each_basic_fidelity_target_fidelity_required_EPRs:
                for path,path_basic_fidelity in self.each_path_basic_fidelity.items():
                    if path_basic_fidelity==basic:
                        for target in targets:
                            required_EPRs = each_basic_fidelity_target_fidelity_required_EPRs[basic][target]
                            try:
                                self.oracle_for_target_fidelity[path][target] = min(required_EPRs)
#                                 print("for path %s to target %s we added %s"%(path,target,min(required_EPRs)))
                            except:
                                self.oracle_for_target_fidelity[path] = {}
                                self.oracle_for_target_fidelity[path][target] = min(required_EPRs)
#                                 print("for path %s to target %s we added %s"%(path,target,min(required_EPRs)))
                                
            for basic,target_EPRs in each_basic_fidelity_target_fidelity_required_EPRs.items():
                self.global_each_basic_fidelity_target_fidelity_required_EPRs[basic] = target_EPRs
                
            for path,path_basic_fidelity in self.each_path_basic_fidelity.items():
                if path_basic_fidelity not in basic_fidelities:
                    for target in targets:
                        required_EPRs = self.global_each_basic_fidelity_target_fidelity_required_EPRs[path_basic_fidelity][target]
                        try:
                            self.oracle_for_target_fidelity[path][target] = min(required_EPRs)
#                             print("from storage: for path %s to target %s we added %s"%(path,target,min(required_EPRs)))
                        except:
                            self.oracle_for_target_fidelity[path] = {}
                            self.oracle_for_target_fidelity[path][target] = min(required_EPRs)
#                             print("from storage: for path %s to target %s we added %s"%(path,target,min(required_EPRs)))
#             for path,target_n in self.oracle_for_target_fidelity.items():
#                 for t,n in target_n.items():
#                     print("for path %s to reach %s we need %s"%(path,t,n))
#             time.sleep(5)
        else:
#             print("we have already computed required EPR pairs to reach threshold for each basic fidelity")
#             time.sleep(10)
            for path,path_basic_fidelity in self.each_path_basic_fidelity.items():
                for target in targets:
                    required_EPRs = self.global_each_basic_fidelity_target_fidelity_required_EPRs[path_basic_fidelity][target]
                    try:
                        self.oracle_for_target_fidelity[path][target] = min(required_EPRs)
#                         print("from storage: for path %s to target %s we added %s"%(path,target,min(required_EPRs)))
                    except:
                        self.oracle_for_target_fidelity[path] = {}
                        self.oracle_for_target_fidelity[path][target] = min(required_EPRs)
                

    def set_storage_capacity(self):
        for storage_node in self.storage_nodes:
            self.each_storage_capacity[storage_node] =1000
    def get_required_edge_level_purification_EPR_pairs(self,edge,p,each_t_requests,t):
        longest_p_lenght   = 0
        max_F_threshold = 0
# #         print("self.each_user_request_fidelity_threshold",self.each_request_threshold)
#         for p,path in self.set_of_paths.items():
#             if edge in path:
                #print("each_t_real_requests ",self.each_t_real_requests)
        for t,users in self.each_t_real_requests.items():
            for user in users:
                #print("self.each_user_pair_real_paths",self.each_user_pair_real_paths)
                if p in self.each_request_real_paths[user]+self.each_request_virtual_paths[user]:
#                     for p2 in self.each_request_real_paths[user]+self.each_request_virtual_paths[user]:
#                         path = self.set_of_paths[p2]
#                         if len(path)>longest_p_lenght:
                    path = self.set_of_paths[p]
                    longest_p_lenght = len(path)
                    if self.each_request_threshold[user][t] > max_F_threshold:
                        max_F_threshold = self.each_request_threshold[user][t]
        if longest_p_lenght==0:
            required_edge_level_fidleity = self.each_edge_fidelity[edge]
            new_target = required_edge_level_fidleity
        else:
            #print("max_F_threshold ",max_F_threshold)
            #print("longest_p_lenght ",longest_p_lenght)
            required_edge_level_fidleity = (3*(4/3*max_F_threshold-1/3)**(1/longest_p_lenght)+1)/4
            new_target = required_edge_level_fidleity
        edge_basic_fidelity = self.each_edge_fidelity[edge]
        try:
            if new_target in self.each_edge_target_fidelity[edge]:
                return self.each_edge_target_fidelity[edge][new_target]
            else:
                n_avg = self.get_avg_epr_pairs_DEJMPS(edge_basic_fidelity ,new_target)
                try:
                    self.each_edge_target_fidelity[edge][new_target] = n_avg
                except:
                    self.each_edge_target_fidelity[edge] = {}
                    self.each_edge_target_fidelity[edge][new_target] = n_avg
                return n_avg
        except:
            if longest_p_lenght==0:
                required_edge_level_fidleity = self.each_edge_fidelity[edge]
                new_target = required_edge_level_fidleity
            else:
                #print("max_F_threshold ",max_F_threshold)
                #print("longest_p_lenght ",longest_p_lenght)
                required_edge_level_fidleity = (3*(4/3*max_F_threshold-1/3)**(1/longest_p_lenght)+1)/4
                new_target = required_edge_level_fidleity
                required_edge_level_fidleity = (3*(4/3*max_F_threshold-1/3)**(1/longest_p_lenght)+1)/4
                new_target = required_edge_level_fidleity
            edge_basic_fidelity = self.each_edge_fidelity[edge]
            n_avg = self.get_avg_epr_pairs_DEJMPS(edge_basic_fidelity ,new_target)
            try:
                self.each_edge_target_fidelity[edge][new_target] = n_avg
            except:
                self.each_edge_target_fidelity[edge] ={}
                self.each_edge_target_fidelity[edge][new_target] = n_avg
            return n_avg
    def get_required_purification_EPR_pairs(self,p,threshold):
#         print("we are getting the required EPR pairs for path %s to reach threshold %s"%(p,threshold))
        
        return self.oracle_for_target_fidelity[p][threshold]
        if threshold>=0.9:
            return self.oracle_for_target_fidelity[p][0.9]
        elif 0.8<threshold<0.9:
            return self.oracle_for_target_fidelity[p][0.8]
        elif threshold<0.8:
            return self.oracle_for_target_fidelity[p][0.7]
        else:
            return 1
    def get_testing_new_storage_pairs(self,number_of_storages): 
        if number_of_storages>0:
            self.storage_pairs.append((2,4))
            self.storage_nodes.append(2)
            self.storage_nodes.append(4)
        else:
            self.storage_pairs= []
            self.storage_nodes= []
    def reset_storage_pairs(self):
        self.storage_pairs=[]
        self.storage_nodes=[]
    def get_new_storage_pairs(self,number_of_storages,storage_node_selection_scheme):
        #print("self.each_t_user_pairs ",self.each_t_user_pairs)
        
        new_selected_storage_nodes = []
        new_selected_storage_pairs = []
        user_pair_nodes = set([])
        all_user_pairs = []
        for t,user_pairs in self.each_t_user_pairs.items():
            for user_pair_id in user_pairs:
#                     print(self.each_id_pair)
                user_pair = self.each_id_pair[user_pair_id]
                user_pair_nodes.add(user_pair[0])
                user_pair_nodes.add(user_pair[1])

                if user_pair not in all_user_pairs:
                    all_user_pairs.append(user_pair)
                if (user_pair[1],user_pair[0]) not in all_user_pairs:
                    all_user_pairs.append((user_pair[1],user_pair[0]))
        user_pair_nodes = list(user_pair_nodes)

        if storage_node_selection_scheme == "Degree":
            each_degree_nodes = {}
            degrees = []
            candidate_nodes = []
            for node in self.g.nodes:
                #if node not in user_pair_nodes:
                    try:
                        each_degree_nodes[self.g.degree[node]].append(node)
                    except:
                        each_degree_nodes[self.g.degree[node]]= [node]
                    degrees.append(self.g.degree[node])
            degrees.sort(reverse=True)
            for degree in degrees:
                nodes = each_degree_nodes[degree]
                for n in nodes:
                    if n not in candidate_nodes:
                        candidate_nodes.append(n)
            #print("candidate_nodes",candidate_nodes)
            if len(candidate_nodes)==0:
                any_available_nodes_for_storage = False
            else:
                any_available_nodes_for_storage = True
            while(len(self.storage_nodes)<number_of_storages and len(candidate_nodes)>0 ): 
                if self.storage_pairs:
                    storage1 = candidate_nodes[0]
                    candidate_nodes.pop(0)
                    for storage_node in self.storage_nodes:
                        if ((storage1,storage_node) not in self.storage_node_pairs and (storage_node,storage1) not in self.storage_node_pairs) and storage1!=storage_node:
                            if (storage1,storage_node) not in all_user_pairs:
                                self.storage_node_pairs.append((storage1,storage_node))
                                self.each_id_pair[self.pair_id] = (storage1,storage_node)
                                self.each_pair_id[(storage1,storage_node)] = self.pair_id
                                self.storage_pairs.append(self.pair_id)
                                self.pair_id+=1

                    if storage1 not in self.storage_nodes:
                        if storage1 not in user_pair_nodes:
                            self.storage_nodes.append(storage1)
                else:
                    if len(candidate_nodes)>1:
                        storage1 = candidate_nodes[0]
                        storage2 = candidate_nodes[1]
                        candidate_nodes.pop(0)
                        candidate_nodes.pop(0)
                        if (storage1,storage2) not in self.storage_node_pairs and (storage2,storage1) not in self.storage_node_pairs:
                            if (storage1,storage2) not in all_user_pairs:
                                self.storage_node_pairs.append((storage1,storage2))
                                self.storage_pairs.append(self.pair_id)
                                self.each_id_pair[self.pair_id] = (storage1,storage2)
                                self.each_pair_id[(storage1,storage2)] = self.pair_id
                                self.pair_id+=1

                                self.storage_nodes.append(storage1)
                                self.storage_nodes.append(storage2)
            
        else:
            
            permitted_nodes = []
            for node in self.nodes:
                if node not in self.storage_nodes:
                    permitted_nodes.append(node)
            #print("we have permitted node as ",permitted_nodes,len(self.storage_nodes),number_of_storages,len(user_pair_nodes),user_pair_nodes)
            if len(permitted_nodes)+len(self.storage_nodes)<=number_of_storages:
                for storage1 in permitted_nodes:
                    for storage2 in permitted_nodes:
                        if storage1 != storage2:
                            if (storage1,storage2) not in self.storage_node_pairs and (storage2,storage1) not in self.storage_node_pairs:
                                if (storage1,storage2) not in all_user_pairs:
                                    self.storage_node_pairs.append((storage1,storage2))
                                    self.storage_pairs.append(self.pair_id)
                                    self.each_id_pair[self.pair_id] = (storage1,storage2)
                                    self.each_pair_id[(storage1,storage2)] = self.pair_id
                                    self.pair_id+=1
                                    
                                    #self.storage_pairs.append((storage1,storage2))
                                    self.storage_nodes.append(storage1)
                                    self.storage_nodes.append(storage2)

            else:
                while(len(self.storage_nodes)<number_of_storages and len(permitted_nodes)>0):
                    
                        
                    #print("we selected new storage node %s"%(storage1))
                    if self.storage_pairs:
                        storage1 = permitted_nodes[random.randint(0,len(permitted_nodes)-1)]
                        for storage_node in self.storage_nodes:
                            if ((storage1,storage_node) not in self.storage_node_pairs and (storage_node,storage1) not in self.storage_node_pairs) and storage1!=storage_node:
                                if (storage1,storage_node) not in all_user_pairs:
                                    self.storage_node_pairs.append((storage1,storage_node))
                                    self.storage_pairs.append(self.pair_id)
                                    self.each_id_pair[self.pair_id] = (storage1,storage_node)
                                    self.each_pair_id[(storage1,storage_node)] = self.pair_id
                                    self.pair_id+=1
                                    
                        if storage1 not in self.storage_nodes:
                            self.storage_nodes.append(storage1)
                    else:
                        storage1 = permitted_nodes[random.randint(0,len(permitted_nodes)-1)]
                        storage2 = storage1
                        while(storage1==storage2):
                            storage2 = permitted_nodes[random.randint(0,len(permitted_nodes)-1)]
                        #print("for round  we have new storage node %s"%(storage1))
                        if (storage1,storage2) not in self.storage_node_pairs and (storage2,storage1) not in self.storage_node_pairs:
                            if (storage1,storage2) not in all_user_pairs:
                                self.storage_node_pairs.append((storage1,storage2))
                                self.storage_pairs.append(self.pair_id)
                                self.each_id_pair[self.pair_id] = (storage1,storage2)
                                self.each_pair_id[(storage1,storage2)] = self.pair_id
                                self.pair_id+=1
                                
                                self.storage_nodes.append(storage1)
                                self.storage_nodes.append(storage2)
    
        
    
    def get_each_user_pair_real_paths(self,pairs_id):
        #print("we are getting all paths for pairs ",pairs)
        for user_pair_id in pairs_id:
            user_pair = self.each_id_pair[user_pair_id]
            shortest_paths = nx.all_shortest_paths(self.g,source=user_pair[0],target=user_pair[1], weight='weight')
            #print(shortest_paths)
            #print(shortest_paths.sort(reverse=True))
            import pdb
            #pdb.set_trace()
            paths = []
            for p in shortest_paths:
                #print("for src %s dst %s shortest path is %s "%(user_pair[0],user_pair[1],p))
                paths.append(p)
            self.each_user_pair_all_real_paths[user_pair_id] = paths
        for user_pair_id in pairs_id:
            user_pair = self.each_id_pair[user_pair_id]
            if user_pair[0]==user_pair[1]:
                paths = [[user_pair[0]]]
            else:
                shortest_disjoint_paths = nx.edge_disjoint_paths(self.g,s=user_pair[0],t=user_pair[1])
                #print(shortest_paths)
                #print(shortest_paths.sort(reverse=True))
                import pdb
                #pdb.set_trace()
                paths = []
                for p in shortest_disjoint_paths:
                    #print("for src %s dst %s shortest disjoint path is %s "%(user_pair[0],user_pair[1],p))
                    #if p not in self.each_user_pair_all_real_paths[user_pair]:
                        #print("We have a path in disjoint that is not in shortest path!!!!")
                        #print("the shortespt paths are ",self.each_user_pair_all_real_paths[user_pair])
                        #time.sleep(4)
                    paths.append(p)
            self.each_user_pair_all_real_disjoint_paths[user_pair_id] = paths
        
        #time.sleep(1)
            
    def set_real_paths(self,pair_of_storages,user_pairs):
        
        for storage_pair_id in pair_of_storages:
            
            storage_pair = self.each_id_pair[storage_pair_id]
            #print("for storage pair id %s pair %s "%(storage_pair_id,storage_pair))
            paths = self.get_real_path(storage_pair_id)
            valid_paths = []
            for path in paths:
                #print("we ahev path ",path)
                if self.get_this_path_fidelity(path)>=0.6:
                    valid_paths.append(self.path_counter_id)
                    self.set_each_path_length(self.path_counter_id,path)
                    self.set_of_paths[self.path_counter_id] = path
                    self.each_storage_path_path_id[tuple(path)] = self.path_counter_id
                    self.path_existance_flag = True
                    try:
                        self.each_request_real_paths[storage_pair_id].append(self.path_counter_id)
                    except:
                        self.each_request_real_paths[storage_pair_id]=[self.path_counter_id]
                    try:
                        self.each_storage_real_paths[storage_pair_id].append(self.path_counter_id)
                    except:
                        self.each_storage_real_paths[storage_pair_id]=[self.path_counter_id]
                    #print("storage_pair %s self.path_counter_id %s for path %s "%(storage_pair_id,self.path_counter_id,path))
                    self.path_counter_id+=1
            if len(valid_paths)==0:
                try:
                    self.each_storage_real_paths[storage_pair_id] = []
                except:
                    self.each_storage_real_paths[storage_pair_id]=[]
                    
                try:
                    self.each_request_real_paths[storage_pair_id] = []
                except:
                    self.each_request_real_paths[storage_pair_id]=[]
        for user_pair_id in user_pairs:
            this_user_pair_has_one_real_path = False
            paths = self.get_real_path(user_pair_id)
            for path in paths:
                if self.get_this_path_fidelity(path)>=0.6:
                    this_user_pair_has_one_real_path = True
                    self.path_existance_flag= True
                    self.set_each_path_length(self.path_counter_id,path)
                    self.set_of_paths[self.path_counter_id] = path
                    self.each_user_path_path_id[tuple(path)] = self.path_counter_id
                    try:
                        self.each_request_real_paths[user_pair_id].append(self.path_counter_id)
                    except:
                        self.each_request_real_paths[user_pair_id]=[self.path_counter_id]
                    #print("user_pair %s self.path_counter_id %s for path %s "%(user_pair_id,self.path_counter_id,path))
                    self.path_counter_id+=1  
            if not this_user_pair_has_one_real_path:
                try:
                    self.each_request_real_paths[user_pair_id]=[]
                except:
                    self.each_request_real_paths[user_pair_id]=[]
    
    def set_virtual_paths(self,across_all_time_slots_pairs_ids):
        all_sub_paths = []
        for user_pair_id in across_all_time_slots_pairs_ids:
            user_pair = self.each_id_pair[user_pair_id]
            #print("for user pair ",user_pair)
            this_user_has_at_least_one_virtual_path_flag = False
            for storage_pair_id in self.storage_pairs:
                """add one new path to the previous paths"""
                #print("to connect to storage pair ",storage_pair_id)
                for real_sub_path_id in self.each_storage_real_paths[storage_pair_id]:
                    #print("for its sub path ",real_sub_path_id)
                    this_sub_path_flag = False
                    real_sub_path = self.set_of_paths[real_sub_path_id]
                    paths = self.get_paths_to_connect_users_to_storage(user_pair,real_sub_path)
                    #print("we have paths ",paths)
                    #this_sub_path_id = self.each_storage_path_path_id[tuple(real_sub_path)]
                    if real_sub_path_id not in all_sub_paths:
                        all_sub_paths.append(real_sub_path_id)
                    for path in paths:
                        
                        if self.get_this_path_fidelity(path)>=0.6:
                            #print("a candidate path %s with id %s"%(path,real_sub_path_id))
                            this_sub_path_flag = True
                            this_user_has_at_least_one_virtual_path_flag = True
                            path = self.remove_storage_pair_real_path_from_path(real_sub_path,path)
                            self.set_each_path_length(self.path_counter_id,path)
                            """we remove the sub path that is connecting two storage pairs 
                            from the path because we do not want to check the edge capacity for the edges of this subpath"""
                            #print("we are adding path counter %s to the virtual include subpath"%(self.path_counter_id))
                            try:
                                self.each_request_virtual_paths_include_subpath[user_pair_id][real_sub_path_id].append(self.path_counter_id)
                            except:
                                try:
                                    self.each_request_virtual_paths_include_subpath[user_pair_id][real_sub_path_id]=[self.path_counter_id]
                                except:
                                    self.each_request_virtual_paths_include_subpath[user_pair_id]={}
                                    self.each_request_virtual_paths_include_subpath[user_pair_id][real_sub_path_id]=[self.path_counter_id]



                            self.set_of_paths[self.path_counter_id] = path
                            try:
                                self.each_request_virtual_paths[user_pair_id].append(self.path_counter_id)
                            except:
                                self.each_request_virtual_paths[user_pair_id]=[self.path_counter_id]
                                    
                            
                            #print("we added %s to the virtual path of %s "%(self.path_counter_id,user_pair))
                            self.path_counter_id+=1
                    if not this_sub_path_flag:
                        try:
                            self.each_request_virtual_paths_include_subpath[user_pair_id][real_sub_path_id]=[]
                        except:
                            self.each_request_virtual_paths_include_subpath[user_pair_id]={}
                            self.each_request_virtual_paths_include_subpath[user_pair_id][real_sub_path_id]=[]

            if not this_user_has_at_least_one_virtual_path_flag:
                
                try:
                    self.each_request_virtual_paths[user_pair_id]=[]
                except:
                    self.each_request_virtual_paths[user_pair_id]=[]
        for pair_id1 in self.storage_pairs:
            try:
                self.each_request_virtual_paths[pair_id1]=[]
            except:
                self.each_request_virtual_paths[pair_id1]=[]

        for j_id in self.storage_pairs:
            for sub_path_id in all_sub_paths:
                try:
                    self.each_request_virtual_paths_include_subpath[j_id][sub_path_id] = []
                except:
                    self.each_request_virtual_paths_include_subpath[j_id]={}
                    self.each_request_virtual_paths_include_subpath[j_id][sub_path_id] = []
#         for t in self.T:
#             for k in self.each_t_requests[t]:
#                 for sub_path_id in all_sub_paths:
#                     try:
#                         if k in list(self.each_request_virtual_paths_include_subpath.keys()):
#                             if sub_path_id not in list(self.each_request_virtual_paths_include_subpath[k].keys()):

#                                 try:
#                                     self.each_request_virtual_paths_include_subpath[k][sub_path_id] = []
#                                 except:
#                                     self.each_request_virtual_paths_include_subpath[k]={}
#                                     self.each_request_virtual_paths_include_subpath[k][sub_path_id] = []
#                             else:
#                                 action= "do nothing!"
#                         else:
#                             for sub_path_id in all_sub_paths:
#                                 try:
#                                     self.each_request_virtual_paths_include_subpath[k][sub_path_id] = []
#                                 except:
#                                     self.each_request_virtual_paths_include_subpath[k]={}
#                                     self.each_request_virtual_paths_include_subpath[k][sub_path_id] = []
#                     except:
#                         for sub_path_id in all_sub_paths:
#                             try:
#                                 self.each_request_virtual_paths_include_subpath[k][sub_path_id] = []
#                             except:
#                                 self.each_request_virtual_paths_include_subpath[k]={}
#                                 self.each_request_virtual_paths_include_subpath[k][sub_path_id] = []

        
        
    def get_real_longest_path(self,user_or_storage_pair,number_of_paths):
        all_paths=[]
        for path in nx.all_simple_paths(self.g,source=user_or_storage_pair[0],target=user_or_storage_pair[1]):
            #all_paths.append(path)

            node_indx = 0
            path_edges = []
            for node_indx in range(len(path)-1):
                path_edges.append((path[node_indx],path[node_indx+1]))
                node_indx+=1
            all_paths.append(path_edges)

        all_paths.sort(key=len,reverse=True)
        if len(all_paths)>=number_of_paths:
            return all_paths[:number_of_paths]
        else:
            return all_paths
                        
    def get_real_path(self,user_or_storage_pair_id):
        if self.path_selection_scheme=="shortest":
            path_selecion_flag = False
            path_counter = 1
            paths = []
            #print("user_or_storage_pair",user_or_storage_pair)
            #print("self.each_user_pair_all_real_paths[user_or_storage_pair]",self.each_user_pair_all_real_paths[user_or_storage_pair])
            for path in self.each_user_pair_all_real_paths[user_or_storage_pair_id]:
                #print("we can add this path",path)
                if path_counter<=self.num_of_paths:
                    node_indx = 0
                    path_edges = []
#                     print("for pair this is the normal path ",user_or_storage_pair,path)
#                     if len(path)==1:
#                         print("this si the unnormal case")
#                         for node_indx in range(len(path)-1):
#                             print("edge",(path[node_indx],path[node_indx+1]))
#                             path_edges.append((path[node_indx],path[node_indx+1]))
#                             node_indx+=1
#                         import pdb
#                         import time
#                         time.sleep(3)
#                         #pdb.set_trace()
                    for node_indx in range(len(path)-1):
                        path_edges.append((path[node_indx],path[node_indx+1]))
                        node_indx+=1
                    paths.append(path_edges)

                path_counter+=1
        elif self.path_selection_scheme=="shortest_disjoint":
            path_selecion_flag = False
            path_counter = 1
            paths = []
            #print("self.each_user_pair_all_real_paths[user_or_storage_pair]",self.each_user_pair_all_real_paths[user_or_storage_pair])
            for path in self.each_user_pair_all_real_disjoint_paths[user_or_storage_pair_id]:
                #print("we can add this path",path)
                if path_counter<=self.num_of_paths:
                    node_indx = 0
                    path_edges = []
#                     print("for pair this is the disjoint path ",user_or_storage_pair,path)
#                     if len(path)==1:
#                         print("this si the unnormal case",path)
#                         for node_indx in range(len(path)-1):
#                             print("edge",(path[node_indx],path[node_indx+1]))
#                             path_edges.append((path[node_indx],path[node_indx+1]))
#                             node_indx+=1
#                         import pdb
#                         #pdb.set_trace()
                    for node_indx in range(len(path)-1):
                        path_edges.append((path[node_indx],path[node_indx+1]))
                        node_indx+=1
                    paths.append(path_edges)

                path_counter+=1
            
        return paths
                    
      
                    
    def connect_users_to_storages(self,user1,storage1,storage2,user2,real_sub_path):
        #print("we are going to connect node %s to %s and %s to %s"%(user1,storage1,storage2,user2))
        if user1==storage1 and storage2==user2:
            set_of_paths= [[]]
             
        elif user1==storage2 and storage1==user2:
            return [[]]
        elif user1==storage1 and storage2!=user2:
            if (storage2,user2) in self.each_pair_id:
                pair_id = self.each_pair_id[(storage2,user2)]
            else:
                self.each_pair_id[(storage2,user2)] = self.pair_id
                pair_id = self.pair_id
                self.each_id_pair[self.pair_id]= (storage2,user2)
                self.pair_id+=1
            self.get_each_user_pair_real_paths([pair_id])
            set_of_paths = self.get_real_path(pair_id)
        elif user1!=storage1 and storage2==user2:
            if (user1,storage1) in self.each_pair_id:
                pair_id = self.each_pair_id[(user1,storage1)]
            else:
                self.each_pair_id[(user1,storage1)] = self.pair_id
                pair_id = self.pair_id
                self.each_id_pair[self.pair_id]= (user1,storage1)
                self.pair_id+=1
            self.get_each_user_pair_real_paths([pair_id])
            set_of_paths = self.get_real_path(pair_id)
        elif user1==storage2 and storage1!=user2:
            if (user2,storage1) in self.each_pair_id:
                pair_id = self.each_pair_id[(user2,storage1)]
            else:
                self.each_pair_id[(user2,storage1)] = self.pair_id
                pair_id = self.pair_id
                self.each_id_pair[self.pair_id]= (user2,storage1)
                self.pair_id+=1
            self.get_each_user_pair_real_paths([pair_id])
            set_of_paths = self.get_real_path(pair_id)
        elif user1!=storage2 and storage1==user2:
            if (user1,storage2) in self.each_pair_id:
                pair_id = self.each_pair_id[(user1,storage2)]
            else:
                self.each_pair_id[(user1,storage2)] = self.pair_id
                pair_id = self.pair_id
                self.each_id_pair[self.pair_id]= (user1,storage2)
                self.pair_id+=1
            self.get_each_user_pair_real_paths([pair_id])
            set_of_paths = self.get_real_path(pair_id)
        else:
            if (user1,storage1) in self.each_pair_id:
                pair_id = self.each_pair_id[(user1,storage1)]
            else:
                self.each_pair_id[(user1,storage1)] = self.pair_id
                pair_id = self.pair_id
                self.each_id_pair[self.pair_id]= (user1,storage1)
                self.pair_id+=1
            self.get_each_user_pair_real_paths([pair_id])
            sub_paths5 = self.get_real_path(pair_id)
            if (storage2,user2) in self.each_pair_id:
                pair_id2 = self.each_pair_id[(storage2,user2)]
            else:
                self.each_pair_id[(storage2,user2)] = self.pair_id
                pair_id2 = self.pair_id
                self.each_id_pair[self.pair_id]= (storage2,user2)
                self.pair_id+=1
            self.get_each_user_pair_real_paths([pair_id2])
            sub_paths6 = self.get_real_path(pair_id2)
            #print("we got these paths for them",sub_paths1,sub_paths2)
            set_of_paths1 = []
            for path_part1 in sub_paths5:
                new_path = []
                for edge in path_part1:
                    new_path.append(edge)
                for edge in real_sub_path:
                    new_path.append(edge)
                
                for path_part2 in sub_paths6:
                    for edge in path_part2:
                        new_path.append(edge)
                    set_of_paths1.append(new_path)
            self.get_each_user_pair_real_paths([pair_id])
            sub_paths52 = self.get_real_path(pair_id)
            self.get_each_user_pair_real_paths([pair_id2])
            sub_paths62 = self.get_real_path(pair_id2)
            #print("we got these paths for them",sub_paths1,sub_paths2)
            set_of_paths2 = []
            for path_part1 in sub_paths5:
                new_path = []
                for edge in path_part1:
                    new_path.append(edge)
                for edge in real_sub_path:
                    new_path.append(edge)
                
                for path_part2 in sub_paths6:
                    for edge in path_part2:
                        new_path.append(edge)
                    set_of_paths2.append(new_path) 
            first_path_length = []
            second_path_length = []
            for path in set_of_paths1:
                first_path_length.append(len(path))
            for path in set_of_paths2:
                second_path_length.append(len(path))
            if sum(first_path_length)/len(first_path_length)>sum(second_path_length)/len(second_path_length):
                set_of_paths =  set_of_paths2
            else:
                set_of_paths =  set_of_paths1
        return set_of_paths
    def get_paths_to_connect_users_to_storage(self,user_pair,real_sub_path):
        #print("we are going to find shortest path to connect user pair %s to sub path %s"%(user_pair,real_sub_path))
        src= user_pair[0]
        dst= user_pair[1]
        str1 = real_sub_path[0][0]
        str2= real_sub_path[len(real_sub_path)-1][1]
        set_of_paths = self.connect_users_to_storages(src,str1,str2,dst,real_sub_path)
        #print("it was path ",set_of_paths)
        return set_of_paths
        
    def set_each_path_basic_fidelity(self):
#         print("self.each_edge_fidelity[edge]",self.each_edge_fidelity)
        #basic_fidelities = [0.7,0.8,0.9]
        self.each_path_basic_fidelity = {}
        for path,path_edges in self.set_of_paths.items():
            #basic_fidelity = basic_fidelities[random.randint(0,len(basic_fidelities)-1)]
            if path_edges:
                #print("this is path id %s and edges %s"%(path,path_edges))
                basic_fidelity = 1/4+(3/4)*(4*self.each_edge_fidelity[path_edges[0]]-1)/3
                #1/4 +3/4((4F1-1)/3)((4F2-1)/3)
                #print("for path %s with lenght %s first edge fidelity %s %s "%(path,self.each_path_legth[path],self.each_edge_fidelity[path_edges[0]],basic_fidelity ))
                for edge in path_edges[1:]:
    #                 basic_fidelity = basic_fidelity * self.each_edge_fidelity[edge]
                    #print("edge with fidelity %s"%(self.each_edge_fidelity[edge]))
                    basic_fidelity  = (basic_fidelity)*((4*self.each_edge_fidelity[edge]-1)/3)
                basic_fidelity = basic_fidelity
            else:
                basic_fidelity = 0.999
            self.each_path_basic_fidelity[path]= round(basic_fidelity,3)
            #if round(basic_fidelity,3)<0.6:
                #print("path end to end fidelity is ",round(basic_fidelity,3))
                #import time
                #time.sleep(10)
    def check_each_request_real_virtual_paths(self):
        for t in self.T[1:]:
            for k in self.each_t_requests[t]:
                having_at_least_one_path_flag = False
                try:
                    if self.each_request_real_paths[k]:
                        for p in self.each_request_real_paths[k]:
                            having_at_least_one_path_flag = True
                except:
                    pass
                try:
                    for p in self.each_request_virtual_paths[k]:
                        having_at_least_one_path_flag = True
                except:
                    pass
                if not having_at_least_one_path_flag:
                    return False
        return having_at_least_one_path_flag
                    
    def check_path_include_sub_path2(self,k,sub_path_id,path_id):
        if path_id in self.each_request_virtual_paths_include_subpath[k][sub_path_id]:
            return True
        else:
            return False   
    def check_path_include_sub_path(self,sub_path,path):
        if self.set_of_paths[sub_path] in self.set_of_paths[path]:
            return True
        else:
            return False
    def get_edges(self):
        return self.set_E
    def get_this_path_fidelity(self,path_edges):
        
        if path_edges:
            basic_fidelity = 1/4+(3/4)*(4*self.each_edge_fidelity[path_edges[0]]-1)/3
            #1/4 +3/4((4F1-1)/3)((4F2-1)/3)
            for edge in path_edges[1:]:
                basic_fidelity  = (basic_fidelity)*((4*self.each_edge_fidelity[edge]-1)/3)
        else:
            basic_fidelity  = 0.999
        return basic_fidelity
    def get_storage_capacity(self,storage):
        return self.each_storage_capacity[storage]
    def check_path_include_edge(self,edge,path):
        #print('edge is %s and path is %s and Paths is %s'%(edge,path,self.set_of_paths))
        if edge in self.set_of_paths[path]:
            return True
        elif edge not  in self.set_of_paths[path]:
            return False
    def check_storage_pair_exist(self,s1,s2):
        if (s1,s2) in self.storage_pairs:
            return True
        else:
            return False
    def check_request_use_path(self,k,p):
        if p in self.each_request_virtual_paths[k] or (p in self.each_request_virtual_paths[k]):
            return True
        else:
            return False
    #         edge_capacity
    #         paths
    #         virtual_paths
    def get_path_length(self,path):
        return self.each_path_legth[path]-1



# In[ ]:





# In[8]:



# G = nx.icosahedral_graph()
# # len(list(nx.edge_disjoint_paths(G, 0, 0)))
# shortest_paths = nx.all_shortest_paths(G,source=0,target=0, weight='weight')
# shortest_disjoint_paths = nx.edge_disjoint_paths(G,s=0,t=6)
# for p in shortest_paths:
#     print(p)
# for p in shortest_disjoint_paths:
#     print("disjoint",p)
# F1 = 1
# F2 = 0.9
# path_edges = [(1,2),(2,3),(3,4)]
# print(path_edges[1:])
# fidelity = (1/4)+(3/4) *((4 *F1-1)/3)*((4*F2-1)/3)
# print(fidelity)
# fidelity = (1+(3*F1*F2))/4
# print(fidelity)


# In[ ]:





# In[ ]:


# selected_storage_nodes = []
# selected_storage_pairs = []
# nodes = [1,2,3,4,5,6,10,11,12,7,8,9]
# network = Network("topology_file_path")
# network.get_each_user_pair_real_paths(network.user_pairs)
# # nx.draw(network.g,with_labels=True)
# # plt.show()
# work_load = Work_load(network.user_pairs)
# for num_of_storages in range(1,2):
#     path_counter_id = 0
#     print("for number of storages round  ",num_of_storages)
#     """select and add new storage pairs"""
#     new_storage_nodes,new_storage_pairs = network.get_new_storage_pairs(num_of_storages)
#     network.get_each_user_pair_real_paths(network.storage_pairs)
#     for pair in network.storage_pairs:
#         for time in work_load.T:
#             work_load.each_t_each_request_demand[time][pair] = 0
#     """we add a new virtual link to the graph"""
# #     for new_pair in new_storage_pairs:
# #         print(new_pair[0],new_pair[1])
# #         network.g.add_edge(new_pair[0],new_pair[1],weight=0)
        
#     each_user_pair_real_paths = {}
#     each_user_pair_virtual_paths = {}
#     """with new storage pairs, we will check the solution for each number of paths(real and virtual)"""
#     for num_paths in range(1,10):
        
#         """first we add the real paths between storage pairs"""
        
#         print("for path number ",num_paths)
#         for storage_pair in network.storage_pairs:
#             paths = network.get_real_path(storage_pair,num_paths)
#             for path in paths:
#                 network.set_of_paths[path_counter_id] = path
#                 try:
#                     network.each_request_real_paths[storage_pair].append(path_counter_id)
#                 except:
#                     network.each_request_real_paths[storage_pair]=[path_counter_id]
#                 path_counter_id+=1
#                 try:
#                     network.each_user_pair_real_paths[storage_pair].append(path)
#                 except:
#                     network.each_user_pair_real_paths[storage_pair]=[path]
#             print("for new storage pair we got real paths and it is")
#             print(network.each_user_pair_real_paths[storage_pair])
#         for user_pair in network.user_pairs:
#             for storage_pair in network.storage_pairs:
#                 """add one new path to the previous paths"""
#                 paths = network.get_real_path(user_pair,num_paths)
#                 for path in paths:
#                     network.set_of_paths[path_counter_id] = path
#                     try:
#                         network.each_request_real_paths[user_pair].append(path_counter_id)
#                     except:
#                         network.each_request_real_paths[user_pair]=[path_counter_id]
#                     path_counter_id+=1
#                     try:
#                         network.each_user_pair_real_paths[user_pair].append(path)
#                     except:
#                         network.each_user_pair_real_paths[user_pair]=[path]
#                 print("for user pair  we got real paths and it is",user_pair)
#                 print(network.each_user_pair_real_paths[user_pair])
#                 for real_sub_path in network.each_user_pair_real_paths[storage_pair]:
#                     #for edge in real_sub_path:
#                         #network.g.remove_edge(edge[0],edge[1])
#                     #network.g.add_edge(storage_pair[0],storage_pair[1],weight=0)
#                     print("we are going to add a virtual path for user pair %s that includes %s"%(user_pair,real_sub_path))
#                     paths = network.get_paths_to_connect_users_to_storage(user_pair,real_sub_path,num_paths)
                    
#                     print(paths)
#                     for path in paths:
#                         network.set_of_paths[path_counter_id] = path
#                         try:
#                             network.each_request_virtual_paths[user_pair].append(path_counter_id)
#                         except:
#                             network.each_request_virtual_paths[user_pair]=[path_counter_id]
#                         path_counter_id+=1
                        
#                         try:
#                             network.each_user_pair_virtual_paths[user_pair].append(path)
#                         except:
#                             network.each_user_pair_virtual_paths[user_pair]=[path]
#                     for pair in network.storage_pairs:
#                         network.each_request_virtual_paths[pair]=[]
#                     #network.get_virtual_path(user_pair,storage_pair,real_sub_path)
#                     #print("for user pair %s to storage pair %s we got real paths and it is:"%(user_pair,storage_pair))
#                     #print(network.each_user_pair_virtual_paths[user_pair])
                
                
                
#                 """solve the optimization"""
                
                


# In[ ]:


# class Work_load(object):
#     def __init__(self):
#         self.T = [0,1,2]
#         self.num_requests = 2
#         self.request_pairs = [(1,6),(2,5),(10,12)]
#         self.each_t_requests = {0:[(1,6),(2,5),(10,12)],1:[(1,6),(2,5),(10,12)],2:[(1,6),(2,5),(10,12)]}
#         self.each_t_real_requests = {1:[(1,6)],2:[(1,6)]}
#         self.time_intervals = 2
#         self.each_t_each_request_demand = {0:{(1,6):10,(2,5):0,(10,12):0},
#                                            1:{(1,6):1,(2,5):0,(10,12):0},2:{(1,6):10,(2,5):0,(10,12):0}}
#         self.each_request_thrshold = {(1,6):{0:0.9,1:0.8,2:0.9},
#                                      (2,5):{0:0.3,1:0.3,2:0.3},
#                                      (10,12):{0:0.3,1:0.3,2:0.3}
#                                      }


# In[ ]:


# # Python3 program to find shortest path
# # with exactly k edges

# # Define number of vertices in the graph
# # and infinite value

# # A naive recursive function to count
# # walks from u to v with k edges
# def shortestPath(graph, u, v, k):
    
#     V = 4
#     INF = 999999999999

#     # Base cases
#     if k == 0 and u == v:
#         return 0
#     if k == 1 and graph[u][v] != INF:
#         print(graph[u][v],(u,v))
#         return graph[u][v],(u,v)
#     if k <= 0:
#         return INF

#     # Initialize result
#     res = INF

#     # Go to all adjacents of u and recur
#     for i in range(V):
#         if graph[u][i] != INF and u != i and v != i:
#             rec_res,edge = shortestPath(graph, i, v, k - 1)
#             if rec_res != INF:
#                 res = min(res, graph[u][i] + rec_res)
#                 print(res,edge)
#     return res

#     # Driver Code
# if __name__ == '__main__':
#     INF = 999999999999

#     # Let us create the graph shown
#     # in above diagram
#     graph = [[0, 8, 3, 2],
#             [INF, 0, INF, 1],
#             [INF, INF, 0, 6],
#             [INF, INF, INF, 0]]
#     u = 0
#     v = 3
#     k = 2
#     print("Weight of the shortest path is",
#             shortestPath(graph, u, v, k))

#     # This code is contributed by PranchalK


# In[ ]:


def generate_random_topologies(topology_sizes):
    not_connected_topologies = []
    import networkx as nx
    for topology_size in topology_sizes:
        avg_degrees = []
        all_diameters = []
        avg_edges = []
        topology_indx = 0
        added_connected_topologies = []
        while(len(added_connected_topologies)<2):
            degrees = []
            graph = nx.erdos_renyi_graph(topology_size, 0.01, seed=None, directed=False)
            
#             graph = nx.barabasi_albert_graph(topology_size, 2)
            set_of_E = set([])
        #     file1 = open("data/random_erdos_renyi2_"+str(i)+".txt", "w")
            try:
                all_diameters.append(nx.diameter(graph))
                added_connected_topologies.append(topology_indx)
#                 file1 = open("data/size_"+str(topology_size)+"_random_barabasi_albert_0_0_1_"+str(topology_indx)+".txt", "w")
                file1 = open("data/size_"+str(topology_size)+"_random_erdos_renyi_0_0_1_"+str(topology_indx)+".txt", "w")

                file1.writelines("Link_index	Source	Destination	Capacity(kbps)"+"\n")
                edge_counter = 0
                for e in graph.edges:
                    #print(e)
                    file1.writelines(str(edge_counter)+"\t"+str(e[0])+"\t"+str(e[1])+"\t"+"1"+"\n")
                    edge_counter+=1
                    set_of_E.add(e)
                #file1.close()
                #print(len(list(set_of_E)))
                avg_edges.append(len(list(set_of_E)))
                try:
                    all_diameters.append(nx.diameter(graph))
                except:
                    not_connected_topologies.append(str(topology_size)+","+str(topology_indx))
                for node in graph.nodes:
                    degrees.append(graph.degree[node])
                avg_degrees.append(sum(degrees)/len(degrees))
            except:
                pass
            topology_indx+=1
        print("avg degree %s and avg edges %s "%(sum(avg_degrees)/len(avg_degrees),sum(avg_edges)/len(avg_edges)))
        print("not_connected_topologies",not_connected_topologies)
        print(all_diameters)
# topology_sizes = [40,60,70,80,90,100,120,140,160]
# topology_sizes = [400]
# generate_random_topologies(topology_sizes)
# for i in range(2):
#     print(i)
# print(all_diameters)


# In[ ]:


# avg_degrees = []
# avg_edges = []
# for i in range(20):
#     degrees = []
#     graph = nx.barabasi_albert_graph(50, 3)
#     set_of_E = set([])
#     file1 = open("data/random_barabasi_albert_"+str(i)+".txt", "w")
#     file1.writelines("Link_index	Source	Destination	Capacity(kbps)"+"\n")
#     edge_counter = 0
#     for e in graph.edges:
#         #print(e)
#         file1.writelines(str(edge_counter)+"\t"+str(e[0])+"\t"+str(e[1])+"\t"+"1"+"\n")
#         edge_counter+=1
#         set_of_E.add(e)
#     #file1.close()
#     #print(len(list(set_of_E)))
#     avg_edges.append(len(list(set_of_E)))
#     for node in graph.nodes:
#         degrees.append(graph.degree[node])
#     avg_degrees.append(sum(degrees)/len(degrees))
# print("avg degree %s and avg edges %s "%(sum(avg_degrees)/len(avg_degrees),sum(avg_edges)/len(avg_edges)))


# In[ ]:





# In[ ]:


# f = open("data/IBM", 'r')
# header = f.readline()
# #f.readline()
# #         self.link_capacities = np.empty((self.num_links))
# #         self.link_weights = np.empty((self.num_links))
# for line in f:
#     line = line.strip()
#     link = line.split('\t')
#     print(line,link)
#     i, s, d, c = link
#     if int(s) not in nodes:
#         nodes.append(int(s))
#     if int(d) not in nodes:
#         nodes.append(int(d))
#     print(s,d)
#     set_E.append((int(s),int(d)))
    


# In[ ]:





# In[ ]:







# In[ ]:


# import networkx as nx
# import matplotlib.pyplot as plt
# g = nx.Graph()
# g.add_edge(1,2,weight=1)
# g.add_edge(2,3,weight=1)
# g.add_edge(3,4,weight=2)
# g.add_edge(4,5,weight=1)
# g.add_edge(5,6,weight=1)
# g.add_edge(2,10,weight=1)
# g.add_edge(10,11,weight=1)
# g.add_edge(11,12,weight=1)
# g.add_edge(12,5,weight=1)
# g.add_edge(2,7,weight=1)
# g.add_edge(7,8,weight=1)
# g.add_edge(8,9,weight=1)
# g.add_edge(9,5,weight=1)
# shortest_paths = nx.all_shortest_paths(g,source=1,target=6, weight='weight')

# for path in shortest_paths:
#     node_indx = 0
#     path_edges = []
#     for node_indx in range(len(path)-1):
#         path_edges.append((path[node_indx],path[node_indx+1]))
#         node_indx+=1
#     print(path_edges)

# import pdb
# pdb.set_trace()
# nx.draw(g,with_labels=True)
# plt.show()
# user_pairs = [(1,6),(2,5),(10,12)]
# selected_paths = {}
# selected_storage_nodes = []
# nodes = [1,2,3,4,5,6,10,11,12,7,8,9]
# for number_of_storages in range(2,10):
#     storage1 = nodes[randint(0,len(nodes)-1)]
#     if selected_storage_nodes:
#         if storage1 not in selected_storage_nodes:
#             for storage_node in selected_storage_nodes:
#                 new_pairs.append(storage1,storage_node)
#         selected_storage_nodes.extend(new_pairs)
#     else:
#         storage2 = storage1
#         while(storage1==storage2):
#             storage2 = nodes[randint(0,len(nodes)-1)]
#         selected_storage_nodes.append((storage1,storage2))
#     print("this is our first storage pair",selected_storage_nodes)
#     for k in range(int(nx.average_shortest_path_length(g)),10):
#         at_least_one_new_path = False
#         for user_pair in user_pairs:
#             if nx.has_path(g, user_pair[0], user_pair[1]):
#                 shortest_paths = nx.all_shortest_paths(g,source=user_pair[0],target=user_pair[1], weight='weight')
#                 path_selecion_flag = False
#                 path_counter = 0
#                 for path in shortest_paths:
#                     if not path_selecion_flag:
#                         try:
#                             if path not in selected_paths[user_pair]:
#                                 print("for k %s user pair %s we have path %s"%(k,user_pair,path))
#                                 if not at_least_one_new_path:
#                                     at_least_one_new_path = True
#                                 selected_paths[user_pair].append(path)
#                                 path_selecion_flag = True
#                         except:
#                             selected_paths[user_pair]=[path]
#                             path_selecion_flag = True
#                             if not at_least_one_new_path:
#                                 at_least_one_new_path = True
#                             print("for k %s user pair %s we have path %s"%(k,user_pair,path))
#                 if not path_selecion_flag:
#                     print("for k %s user pair %s we have path %s"%(k,user_pair,path))
#         if at_least_one_new_path:
#             print("do the rest of the optimization")
#         else:
#             print("better stop becasue no new paths")



# In[ ]:


def get_topologies_properties(topology_sizes):
    for topology_size in topology_sizes:
        try:
            import networkx as nx
            list_of_topologies = []

    #         list_of_topologies = ["data/ATT_topology_file",'data/abilene','data/Surfnet',"data/IBM"]
            for i in range(2):
    #             list_of_topologies.append("data/random_erdos_renyi2_"+str(i)+".txt")
    #             list_of_topologies.append("data/random_barabasi_albert2_"+str(i)+".txt")
    #             list_of_topologies.append("data/random_erdos_renyi2_"+str(i)+".txt")
#                 list_of_topologies.append("data/random_barabasi_albert2_"+str(i)+".txt")
#                 list_of_topologies.append("data/size_"+str(topology_size)+"_random_barabasi_albert_"+str(i)+".txt")
                list_of_topologies.append("data/size_"+str(400)+"_random_erdos_reni_0_0_1_"+str(i)+".txt")
            all_degrees=[]
            all_edges=[]
            all_diameters=[]
            for top in list_of_topologies:
                print("for topology",top)
                graph = nx.Graph()
                set_of_E = set([])
                f = open(top, 'r')
                header = f.readline()
                #f.readline()
                #         self.link_capacities = np.empty((self.num_links))
                #         self.link_weights = np.empty((self.num_links))
                for line in f:
                    line = line.strip()
                    link = line.split('\t')

                    i, s, d, c = link
                    graph.add_edge(s,d,weight=1)
                    set_of_E.add((s,d))

                degrees = []
                for node in graph.nodes:
                    degrees.append(graph.degree[node])
                print("for topology %s we have #nodes %s edges %s degree %s diameter %s"%
                      (top,len(graph.nodes),len(list(set_of_E)),sum(degrees)/len(degrees),nx.diameter(graph)))
                all_degrees.append(sum(degrees)/len(degrees))
                all_edges.append(len(list(set_of_E)))
                all_diameters.append(nx.diameter(graph))
            print("avg edges %s avg degree %s avg diameter %s "%
                  (sum(all_edges)/len(all_edges),sum(all_degrees)/len(all_degrees),sum(all_diameters)/len(all_diameters)))

            #     print("degree is ",sum(degrees)/len(degrees))
            #     print("edges is ",len(list(set_of_E)))
            #     print("nodes is ",len(graph.nodes))
        except ValueError:
            print(ValueError)
            pass
        
# topology_sizes = [400]
# get_topologies_properties(topology_sizes)
#2,4,6,9,12,13,15,16,17,18


# In[28]:


# not_connected_topologies = []
# topology_sizes = [30]
# import networkx as nx
# for topology_size in topology_sizes:
#     avg_degrees = []
#     all_diameters = []
#     avg_edges = []
#     topology_indx = 0
    
#     degrees = []
#     graph = nx.Graph()
#     for i in range(0,topology_size):
#         if i>0:
#             #print("adding ",i, i-1)
#             graph.add_edge(i, i-1)
#         #print("adding ",i, i+1)
#         graph.add_edge(i, i+1)

#     set_of_E = set([])
#     try:
#         all_diameters.append(nx.diameter(graph))
        
#         file1 = open("data/linear_topology_"+str(topology_size)+".txt", "w")

#         file1.writelines("Link_index	Source	Destination	Capacity(kbps)"+"\n")
#         edge_counter = 0
#         for e in graph.edges:
#             #print(e)
#             file1.writelines(str(edge_counter)+"\t"+str(e[0])+"\t"+str(e[1])+"\t"+"1"+"\n")
#             edge_counter+=1
#             set_of_E.add(e)
#             file1.writelines(str(edge_counter)+"\t"+str(e[1])+"\t"+str(e[0])+"\t"+"1"+"\n")
#             edge_counter+=1
#             set_of_E.add(e)
        
#         avg_edges.append(len(list(set_of_E)))
#         try:
#             all_diameters.append(nx.diameter(graph))
#         except:
#             not_connected_topologies.append(str(topology_size)+","+str(topology_size))
#         for node in graph.nodes:
#             degrees.append(graph.degree[node])
#         avg_degrees.append(sum(degrees)/len(degrees))
#     except ValueError:
#         print(ValueError)
#         pass
#     topology_indx+=1
#     print("avg degree %s and avg edges %s "%(sum(avg_degrees)/len(avg_degrees),sum(avg_edges)/len(avg_edges)))
#     print("not_connected_topologies",not_connected_topologies)
#     print(all_diameters)


# In[12]:


F = 0.94
p = 4
y = (3*(4/3*F-1/3)**(1/p)+1)/4
print(y)

print(1/4 + (3/4*((4*y-1)/3)**4))


# In[ ]:




