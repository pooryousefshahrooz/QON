#!/usr/bin/env python
# coding: utf-8

# In[ ]:





# In[ ]:



import csv
from network import Network
#from workload import Work_load
# from docplex.mp.progress import *
# from docplex.mp.progress import SolutionRecorder
import os
import sys
import pandas as pd
from docplex.mp.progress import *
from docplex.mp.progress import SolutionRecorder
import networkx as nx
import time
from config import get_config
from absl import flags
FLAGS = flags.FLAGS


# In[ ]:


def CPLEX_resource_consumption_minimization_edge_level(network,life_time,iteration,cyclic_workload,storage_capacity,delat_value):
    #print("we are in edge level purificaiton ")
    if cyclic_workload =="cyclic":
        cyclic_workload=True
    else:
        cyclic_workload= False
    import docplex.mp.model as cpx
    opt_model = cpx.Model(name="Storage problem model"+str(iteration))
    w_vars = {}
    u_vars = {}
#     print("we are going to print path info")
    
    
#     print("we are going to print path info")
#     print("each_t_real_request ",network.each_t_real_requests)
#     print("each_t_all_request ",network.each_t_requests)
#     print("storage pairs ",network.storage_pairs)
#     for t in network.T:
#         for k in network.each_t_requests[t]:
#             for p in network.each_request_real_paths[k]:
#                 print("request %s real path is %s"%(k,p))
#             print("real paths are done")
#             for p in network.each_request_virtual_paths[k]:
#                 print("request %s virtual path %s "%(k,p))
#             print("virtual paths are done!")
#     print("we printed paths info")
    w_vars  = {(t,k,p): opt_model.continuous_var(lb=0, ub= network.max_edge_capacity,
                              name="w_{0}_{1}_{2}".format(t,k,p))  for t in network.T 
               for k in network.each_t_requests[t] 
               for p in network.each_request_real_paths[k]+network.each_request_virtual_paths[k]}

    u_vars  = {(t,j,p): opt_model.continuous_var(lb=0, ub= network.max_edge_capacity,
                                  name="u_{0}_{1}_{2}".format(t,j,p))  for t in network.T 
                   for j in network.storage_pairs for p in network.each_request_real_paths[j]}   

    if life_time ==1000:
        #inventory evolution constraint
        for t in network.T[1:]:
            for j in network.storage_pairs:
                for p_s in network.each_request_real_paths[j]:
                    
 
                    if cyclic_workload:
                        opt_model.add_constraint(u_vars[t,j,p_s] == u_vars[(t-1)%len(network.T),j,p_s]-
                        opt_model.sum(w_vars[(t-1)%len(network.T),k,p]
                        
                        for k in network.each_t_requests[t] if k!=j 
                        for p in network.each_request_virtual_paths_include_subpath[k][p_s])*delat_value
                        +opt_model.sum(w_vars[(t-1)%len(network.T),j,p_s])*delat_value
                                             , ctname="inventory_evolution_{0}_{1}".format(t,j,p_s))
                    else:
                        opt_model.add_constraint(u_vars[t,j,p_s] == u_vars[t-1,j,p_s]-
                        opt_model.sum(w_vars[t-1,k,p] 
                        
                        for k in network.each_t_requests[t] if k!=j 
                        for p in network.each_request_virtual_paths_include_subpath[k][p_s])*delat_value
                        +opt_model.sum(w_vars[t-1,j,p_s])*delat_value
                                             , ctname="inventory_evolution_{0}_{1}".format(t,j,p_s))
    else:
        #inventory evolution constraint
        for t in network.T[1:]:
            for j in network.storage_pairs:
                for p_s in network.each_request_real_paths[j]:
                    
                    if cyclic_workload:
                        opt_model.add_constraint(u_vars[t,j,p_s] == -
                        opt_model.sum(w_vars[(t-1)%len(network.T),k,p] 
                        
                        for k in network.each_t_requests[t] if k!=j 
                        for p in network.each_request_virtual_paths_include_subpath[k][p_s] 
                        )*delat_value
                        + opt_model.sum(w_vars[(t-1)%len(network.T),j,p_s])*delat_value
                                             , ctname="inventory_evolution_{0}_{1}".format(t,j,p_s))
                    else:
                        opt_model.add_constraint(u_vars[t,j,p_s] == -
                        opt_model.sum(w_vars[t-1,k,p] 
                        
                        for k in network.each_t_requests[t] if k!=j 
                        for p in network.each_request_virtual_paths_include_subpath[k][p_s] 
                        )*delat_value
                        + opt_model.sum(w_vars[t-1,j,p_s])*delat_value
                                             , ctname="inventory_evolution_{0}_{1}".format(t,j,p_s))

    # serving from inventory constraint
    for t in network.T[1:]:
        for j in network.storage_pairs:
            
            for p_s in network.each_request_real_paths[j]:

                opt_model.add_constraint(opt_model.sum(w_vars[t,k,p]
                
                for k in network.each_t_requests[t] if k!=j 
                for p in network.each_request_virtual_paths_include_subpath[k][p_s] 
                if k in list(network.each_request_virtual_paths_include_subpath.keys()))*delat_value<=u_vars[t,j,p_s]
                                     , ctname="inventory_serving_{0}_{1}_{2}".format(t,j,p_s))  
 
     
    # Demand constriant
    for t in network.T[1:]:
        for k in  network.each_t_requests[t]:
            opt_model.add_constraint(opt_model.sum(w_vars[t,k,p]
            for p in network.each_request_real_paths[k]+network.each_request_virtual_paths[k]) >= 
                    network.each_t_each_request_demand[t][k], ctname="constraint_{0}_{1}".format(t,k))
    
    #Edge constraint
    for t in network.T:
        for edge in network.set_E:
            opt_model.add_constraint(
                opt_model.sum(w_vars[t,k,p]*network.get_required_edge_level_purification_EPR_pairs(edge,p,network.each_t_requests[t],t) for k in network.each_t_requests[t]
                for p in network.each_request_real_paths[k]+network.each_request_virtual_paths[k] if network.check_path_include_edge(edge,p))
                                     
                 <= network.each_edge_capacity[edge], ctname="edge_capacity_{0}_{1}".format(t,edge))
     
    # storage servers capacity constraint
#     storage_capacity = storage_capacity/delat_value
    for t in network.T:
        #for s1 in network.storage_nodes:
        for j in network.storage_pairs:
            opt_model.add_constraint(opt_model.sum(u_vars[t,j,p]
                for p in network.each_request_real_paths[j]) <= storage_capacity 
        , ctname="storage_capacity_constraint_{0}_{1}".format(t,j))
            
#     for t in work_load.T:
#         for s1 in network.storage_nodes:
#             opt_model.add_constraint(opt_model.sum(u_vars[t,(s1,s2),p] 
#                 for s2 in network.storage_nodes if network.check_storage_pair_exist(s1,s2)
#                 for p in network.each_request_real_paths[(s1,s2)])
#         <= storage_capacity, ctname="storage_capacity_constraint_{0}_{1}".format(t,s1))
    
    # constraints for serving from storage at time zero and 1 should be zero
    if not cyclic_workload:
        for t in [0,1]:
            opt_model.add_constraint(opt_model.sum(w_vars[t,k,p]
                    for k in network.each_t_requests[t] for p in network.each_request_virtual_paths[k] 
                    )<=0, ctname="serving_from_inventory_{0}".format(t))
    
    # constraints for putting in storage at time zero  should be zero
    """this is becasue we start the formulation from 1 and not from zero and we have t-1 in our formulation"""
    for t in [0]:
        opt_model.add_constraint(opt_model.sum(w_vars[t,k,p]
                for k in network.each_t_requests[t] for p in network.each_request_real_paths[k] 
                )<=0, ctname="storing_in_inventory_{0}".format(t))   
    

    # constraint for inventory is zero at time zero 
    if not cyclic_workload:
        for t in [0]:
            for j in network.storage_pairs:
                 for p_s in network.each_request_real_paths[j]:
                        opt_model.add_constraint(u_vars[t,j,p_s] <=0, ctname="storage_capacity_constraint_{0}_{1}_{2}".format(t,j,p_s))
    
    """defining an objective, which is a linear expression"""

    objective = opt_model.sum(1/len(network.T[1:])*1/len(network.each_t_real_requests[t])*1/network.each_t_each_request_demand[t][k]
                              *(w_vars[t,k,p] * network.get_path_length(p)) for t in network.T[1:]
                              for k in network.each_t_real_requests[t] 
                              for p in network.each_request_real_paths[k]+network.each_request_virtual_paths[k]
                              )

    
  
    opt_model.minimize(objective)
    
#     opt_model.print_information()
    
    opt_model.solve()

    
#     print('docplex.mp.solution',opt_model.solution)
    objective_value = -1
    try:
        if opt_model.solution:
            objective_value =opt_model.solution.get_objective_value()
    except ValueError:
        print(ValueError)

    each_inventory_per_time_usage = {}
    each_time_each_path_delivered_EPRs = {}
    each_time_each_path_purification_EPRs = {}
    if objective_value>0:
        
#         for t in work_load.T[1:]:
#             for k in work_load.each_t_real_requests[t]:
#                 for p in network.each_request_virtual_paths[k]:
#                     if network.get_path_length(p)==1:
                        #print("this is the path length for path %s "%(network.get_path_length(p)))
                        #print("k is ",k)
                        #print(network.storage_pairs)
        
        time.sleep(5)
        for t in network.T[1:]:
            for k in network.each_t_real_requests[t]: 
                for p in network.each_request_real_paths[k]+network.each_request_virtual_paths[k]:
                    try:
                        each_time_each_path_delivered_EPRs[t][k]+=w_vars[t,k,p].solution_value
                    except:
                        try:
                            each_time_each_path_delivered_EPRs[t][k]= w_vars[t,k,p].solution_value
                        except:
                            each_time_each_path_delivered_EPRs[t]={}
                            each_time_each_path_delivered_EPRs[t][k]= w_vars[t,k,p].solution_value
        
                    try:
                        each_time_each_path_purification_EPRs[t][k]+=network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t))
                    except:
                        try:
                            each_time_each_path_purification_EPRs[t][k]= network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t))
                        except:
                            each_time_each_path_purification_EPRs[t]={}
                            each_time_each_path_purification_EPRs[t][k]= network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t))        
        for t in network.T[1:]:
            for j in network.storage_pairs:
                for p in network.each_request_real_paths[j]:
                    try:
                        each_inventory_per_time_usage[j][t]=u_vars[t,j,p].solution_value
                    except:
                        try:
                            each_inventory_per_time_usage[j][t]=u_vars[t,j,p].solution_value
                        except:
                            each_inventory_per_time_usage[j] = {}
                            each_inventory_per_time_usage[j][t]=u_vars[t,j,p].solution_value        
        
    opt_model.clear()
   
    return objective_value,each_inventory_per_time_usage,each_time_each_path_delivered_EPRs,each_time_each_path_purification_EPRs


# In[ ]:


def CPLEX_resource_consumption_minimization(network,life_time,iteration,cyclic_workload,storage_capacity,delat_value):
    #print("we are in end level purificaiton ")
    if cyclic_workload =="cyclic":
        cyclic_workload=True
    else:
        cyclic_workload= False
    import docplex.mp.model as cpx
    opt_model = cpx.Model(name="Storage problem model"+str(iteration))
    w_vars = {}
    u_vars = {}
#     print("we are going to print path info")
#     print("each_t_real_request ",network.each_t_real_requests)
#     print("each_t_all_request ",network.each_t_requests)
#     print("storage pairs keys ",network.storage_pairs)
#     print("network.pair_id",network.pair_id)
#     print("storage pairs ",network.storage_pairs)
#     for t in network.T:
#         for k in network.each_t_requests[t]:
#             print("for k real ",k)
#             for p in network.each_request_real_paths[k]:
#                 print("request %s real path is %s"%(k,p))
#             print("for k virtual ",k)
#             for p in network.each_request_virtual_paths[k]:
#                 print("request %s virtual path %s "%(k,p))
#     print("we printed paths info")
    w_vars  = {(t,k,p): opt_model.continuous_var(lb=0, ub= network.max_edge_capacity,
                              name="w_{0}_{1}_{2}".format(t,k,p))  for t in network.T 
               for k in network.each_t_requests[t] 
               for p in network.each_request_real_paths[k]+network.each_request_virtual_paths[k]}

    u_vars  = {(t,j,p): opt_model.continuous_var(lb=0, ub= network.max_edge_capacity,
                                  name="u_{0}_{1}_{2}".format(t,j,p))  for t in network.T 
                   for j in network.storage_pairs for p in network.each_request_real_paths[j]}   

    if life_time ==1000:
        #inventory evolution constraint
        for t in network.T[1:]:
            for j in network.storage_pairs:
                for p_s in network.each_request_real_paths[j]:
                    
                    #print("constraint evolution")
                    if cyclic_workload:
                        opt_model.add_constraint(u_vars[t,j,p_s] == u_vars[(t-1)%len(network.T),j,p_s]-
                        opt_model.sum(w_vars[(t-1)%len(network.T),k,p] *
                        network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t))
                        for k in network.each_t_requests[t] if k!=j 
                        for p in network.each_request_virtual_paths_include_subpath[k][p_s])*delat_value
                        +opt_model.sum(w_vars[(t-1)%len(network.T),j,p_s])*delat_value
                                             , ctname="inventory_evolution_{0}_{1}".format(t,j,p_s))
                    else:
                        opt_model.add_constraint(u_vars[t,j,p_s] == u_vars[t-1,j,p_s]-
                        opt_model.sum(w_vars[t-1,k,p] *
                        network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t))
                        for k in network.each_t_requests[t] if k!=j 
                        for p in network.each_request_virtual_paths_include_subpath[k][p_s])*delat_value
                        +opt_model.sum(w_vars[t-1,j,p_s])*delat_value
                                             , ctname="inventory_evolution_{0}_{1}".format(t,j,p_s))
    else:
        #inventory evolution constraint
        for t in network.T[1:]:
            for j in network.storage_pairs:
                for p_s in network.each_request_real_paths[j]:
                    #print("constraint evolution2 ")
                    if cyclic_workload:
                        opt_model.add_constraint(u_vars[t,j,p_s] == -
                        opt_model.sum(w_vars[(t-1)%len(network.T),k,p] *
                        network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t))
                        for k in network.each_t_requests[t] if k!=j 
                        for p in network.each_request_virtual_paths_include_subpath[k][p_s] 
                        )*delat_value
                        + opt_model.sum(w_vars[(t-1)%len(network.T),j,p_s])*delat_value
                                             , ctname="inventory_evolution_{0}_{1}".format(t,j,p_s))
                    else:
                        opt_model.add_constraint(u_vars[t,j,p_s] == -
                        opt_model.sum(w_vars[t-1,k,p] *
                        network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t))
                        for k in network.each_t_requests[t] if k!=j 
                        for p in network.each_request_virtual_paths_include_subpath[k][p_s] 
                        )*delat_value
                        + opt_model.sum(w_vars[t-1,j,p_s])*delat_value
                                             , ctname="inventory_evolution_{0}_{1}".format(t,j,p_s))

    # serving from inventory constraint
    for t in network.T[1:]:
        for j in network.storage_pairs:
            #print("constraint inventory sevging")
            for p_s in network.each_request_real_paths[j]:
                
                opt_model.add_constraint(opt_model.sum(w_vars[t,k,p]*
                network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t))
                for k in network.each_t_requests[t] if k!=j 
                for p in network.each_request_virtual_paths_include_subpath[k][p_s] 
                if k in list(network.each_request_virtual_paths_include_subpath.keys()))*delat_value<=u_vars[t,j,p_s]
                                     , ctname="inventory_serving_{0}_{1}_{2}".format(t,j,p_s))  
 
     
    # Demand constriant
    for t in network.T[1:]:
        for k in  network.each_t_requests[t]:
            #print("constraint demand t %s k %s demand %s"%(t,k,network.each_t_each_request_demand[t][k]))
            opt_model.add_constraint(opt_model.sum(w_vars[t,k,p]
            for p in network.each_request_real_paths[k]+network.each_request_virtual_paths[k]) >= 
                    network.each_t_each_request_demand[t][k], ctname="constraint_{0}_{1}".format(t,k))
    
    #Edge constraint
    for t in network.T:
        for edge in network.set_E:
            #print("edge constraint")
            opt_model.add_constraint(
                opt_model.sum(w_vars[t,k,p]*network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t)) for k in network.each_t_requests[t]
                for p in network.each_request_real_paths[k]+network.each_request_virtual_paths[k] if network.check_path_include_edge(edge,p))
                                     
                 <= network.each_edge_capacity[edge], ctname="edge_capacity_{0}_{1}".format(t,edge))
     
    # storage servers capacity constraint
#     storage_capacity = storage_capacity/delat_value
    for t in network.T:
        #for s1 in network.storage_nodes:
        for j in network.storage_pairs:
            #print("storage capacity constraint")
            opt_model.add_constraint(opt_model.sum(u_vars[t,j,p]
                for p in network.each_request_real_paths[j]) <= storage_capacity 
        , ctname="storage_capacity_constraint_{0}_{1}".format(t,j))
            
#     for t in work_load.T:
#         for s1 in network.storage_nodes:
#             opt_model.add_constraint(opt_model.sum(u_vars[t,(s1,s2),p] 
#                 for s2 in network.storage_nodes if network.check_storage_pair_exist(s1,s2)
#                 for p in network.each_request_real_paths[(s1,s2)])
#         <= storage_capacity, ctname="storage_capacity_constraint_{0}_{1}".format(t,s1))
    
    # constraints for serving from storage at time zero and 1 should be zero
    if not cyclic_workload:
        for t in [0,1]:
            #print("constraints for serving from storage at time zero")
            opt_model.add_constraint(opt_model.sum(w_vars[t,k,p]
                    for k in network.each_t_requests[t] for p in network.each_request_virtual_paths[k] 
                    )<=0, ctname="serving_from_inventory_{0}".format(t))
    
    # constraints for putting in storage at time zero  should be zero
    """this is becasue we start the formulation from 1 and not from zero and we have t-1 in our formulation"""
    for t in [0]:
        #print("constraints becasue we start the formulation from 1 and not")
        opt_model.add_constraint(opt_model.sum(w_vars[t,k,p]
                for k in network.each_t_requests[t] for p in network.each_request_real_paths[k] 
                )<=0, ctname="storing_in_inventory_{0}".format(t))   
    

    # constraint for inventory is zero at time zero 
    if not cyclic_workload:
        for t in [0]:
            #print("constraints constraint for inventory is zero at time zero ")
            for j in network.storage_pairs:
                 for p_s in network.each_request_real_paths[j]:
                        opt_model.add_constraint(u_vars[t,j,p_s] <=0, ctname="storage_capacity_constraint_{0}_{1}_{2}".format(t,j,p_s))
    
    """defining an objective, which is a linear expression"""

    objective = opt_model.sum(1/len(network.T[1:])*1/len(network.each_t_real_requests[t])*1/network.each_t_each_request_demand[t][k]
                              *(w_vars[t,k,p] * network.get_path_length(p)) for t in network.T[1:]
                              for k in network.each_t_real_requests[t] 
                              for p in network.each_request_real_paths[k]+network.each_request_virtual_paths[k]
                              )

    
  
    opt_model.minimize(objective)
    
#     opt_model.print_information()
    
    opt_model.solve()

    
#     print('docplex.mp.solution',opt_model.solution)
    objective_value = -1
    try:
        if opt_model.solution:
            objective_value =opt_model.solution.get_objective_value()
    except ValueError:
        print(ValueError)

    each_inventory_per_time_usage = {}
    each_time_each_path_delivered_EPRs = {}
    each_time_each_path_purification_EPRs = {}
    if objective_value>0:
        
#         for t in work_load.T[1:]:
#             for k in work_load.each_t_real_requests[t]:
#                 for p in network.each_request_virtual_paths[k]:
#                     if network.get_path_length(p)==1:
                        #print("this is the path length for path %s "%(network.get_path_length(p)))
                        #print("k is ",k)
                        #print(network.storage_pairs)
        
        time.sleep(5)
        for t in network.T[1:]:
            for k in network.each_t_real_requests[t]: 
                for p in network.each_request_real_paths[k]+network.each_request_virtual_paths[k]:
                    try:
                        each_time_each_path_delivered_EPRs[t][k]+=w_vars[t,k,p].solution_value
                    except:
                        try:
                            each_time_each_path_delivered_EPRs[t][k]= w_vars[t,k,p].solution_value
                        except:
                            each_time_each_path_delivered_EPRs[t]={}
                            each_time_each_path_delivered_EPRs[t][k]= w_vars[t,k,p].solution_value
        
                    try:
                        each_time_each_path_purification_EPRs[t][k]+=network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t))
                    except:
                        try:
                            each_time_each_path_purification_EPRs[t][k]= network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t))
                        except:
                            each_time_each_path_purification_EPRs[t]={}
                            each_time_each_path_purification_EPRs[t][k]= network.get_required_purification_EPR_pairs(p,network.get_each_request_threshold(k,t))        
        for t in network.T[1:]:
            for j in network.storage_pairs:
                for p in network.each_request_real_paths[j]:
                    try:
                        each_inventory_per_time_usage[j][t]=u_vars[t,j,p].solution_value
                    except:
                        try:
                            each_inventory_per_time_usage[j][t]=u_vars[t,j,p].solution_value
                        except:
                            each_inventory_per_time_usage[j] = {}
                            each_inventory_per_time_usage[j][t]=u_vars[t,j,p].solution_value        
        
    opt_model.clear()
   
    return objective_value,each_inventory_per_time_usage,each_time_each_path_delivered_EPRs,each_time_each_path_purification_EPRs


# In[ ]:


def feasibility(each_network_topology_file,results_file_path,inventory_utilization_results_file_path,delived_purification_EPRs_file_path,number_of_user_pairs,number_of_time_slots, spike_means,num_spikes,experiment_repeat,storage_node_selection_schemes,fidelity_threshold_ranges,cyclic_workload,storage_capacities,given_life_time_set,distance_between_users,setting_demands,edge_fidelity_ranges):
    
    config = get_config(FLAGS) or FLAGS
    for edge_fidelity_range in edge_fidelity_ranges:
        for network_topology,file_path in each_network_topology_file.items():
            for spike_mean in each_topology_mean_value_spike[network_topology]:
                import pdb
                each_storage_each_path_number_value = {}
                network = Network(config,file_path,False,edge_fidelity_range,max_edge_capacity_value,fidelity_threshold_ranges)

                for i in range(experiment_repeat):
                    network.reset_variables()
                    network.get_user_pairs(number_of_user_pairs,distance_between_users,number_of_time_slots)
                    #work_load = Work_load(number_of_time_slots,"time_demands_file.csv")
                    """we set the demands for each user pair"""
                    if setting_demands=="python_library":
                        network.set_each_user_pair_demands(number_of_time_slots,network.each_t_user_pairs,spike_mean,num_spikes)
                    else:
                        network.set_each_user_pair_demands_randomly(number_of_time_slots,network.each_t_user_pairs,spike_mean,num_spikes)
                    """we set at least one demand for each time to avoid divided by zero error"""
                    network.check_demands_per_each_time(network.each_t_user_pairs)                                      
                    for storage_capacity in storage_capacities:
                        for fidelity_threshold_range in fidelity_threshold_ranges:
                            network.fidelity_threshold_range = fidelity_threshold_range
                            network.set_each_request_fidelity_threshold()
#                             print("self.each_request_threshold ",network.each_request_threshold)
                            for storage_node_selection_scheme in storage_node_selection_schemes:
                                selected_storage_nodes = []
                                selected_storage_pairs = []
                                for num_paths in [1]:
                                    network.reset_storage_pairs()
                                    for number_of_storages in [0,2,4,8,10]:
                                        try:
                                            """with new storage pairs, we will check the solution for each number of paths(real and virtual)"""
                                            
                                            pairs = []
                                            """select and add new storage pairs"""
                                            available_flag = network.get_new_storage_pairs(number_of_storages,storage_node_selection_scheme)
                                            network.set_each_storage_fidelity_threshold()
                                            network.set_paths_in_the_network()
                                            
                                            for delat_value in delat_values:
                                                for life_time in given_life_time_set:
                                                    for purificaion_scheme in purification_schemes:
                                                        
                                                        objective_value=-1
                                                        if network.path_existance_flag:
#                                                             print("self.each_request_threshold ",network.each_request_threshold)
                                                            #print("this is the number of storages ",number_of_storages)
                                                            try:
                                                                if purificaion_scheme =="end_level":
                                                                    objective_value,each_inventory_per_time_usage,each_time_each_path_delivered_EPRs,each_time_each_path_purification_EPRs = CPLEX_resource_consumption_minimization(network,life_time,i,cyclic_workload,storage_capacity,delat_value)
                                                                else:
                                                                    objective_value,each_inventory_per_time_usage,each_time_each_path_delivered_EPRs,each_time_each_path_purification_EPRs = CPLEX_resource_consumption_minimization_edge_level(network,life_time,i,cyclic_workload,storage_capacity,delat_value)
                                                            except ValueError:
                                                                print(ValueError)
                                                        else:
                                                            print("oops we do not have even one path for one k at a time!!")
                                                            objective_value = -1
#                                                             for t in network.T:
#                                                                 for k in network.each_t_requests[t]:
#                                                                     for p in network.each_request_real_paths[k]:
#                                                                         print("request %s real path is %s"%(k,p))
#                                                                     for p in network.each_request_virtual_paths[k]:
#                                                                         print("request %s virtual path %s "%(k,p))
                                                        


                                                        print("for purificaion %s topology %s iteration %s from %s spike mean %s capacity %s  fidelity range %s  life time %s storage %s and path number %s objective_value %s"%
                                                        (purificaion_scheme,network_topology,i,experiment_repeat, spike_mean,storage_capacity,fidelity_threshold_range,life_time, number_of_storages,num_paths, objective_value))  
                                                        #print("storage nodes",len(network.storage_nodes),len(network.storage_pairs))

                                                        with open(results_file_path, 'a') as newFile:                                
                                                            newFileWriter = csv.writer(newFile)
                                                            newFileWriter.writerow([network_topology,number_of_storages,num_paths,
                                                                                    life_time,
                                                                                    objective_value,spike_mean,num_spikes,i,
                                                                                    storage_node_selection_scheme,
                                                                                    fidelity_threshold_range,cyclic_workload,
                                                                                    distance_between_users,storage_capacity,edge_fidelity_range,delat_value,purificaion_scheme]) 
                                            
                                        except:
#                                             print(ValueError)
                                            pass


# In[ ]:




experiment_repeat =100 #indicates the number of times that we repeat the experiment

num_spikes = 3 # shows the number of nodes that have spike in their demand. Should be less than the number of user pairs
delat_values = [20]# each time interval is 1 minute or 60 seconds
setting_demands = sys.argv[1] # indicates the way we generate the demands. python_library for using tgem library. random for generating a random demand
number_of_user_pairs =int(sys.argv[2])
spike_means = [1] # list of mean value for spike model traffic generation
edge_fidelity_ranges = [(0.94,0.94)]
max_edge_capacity_value = 1400
path_selection_scheme = "shortest"
purification_schemes = ["end_level","edge_level"]
each_topology_mean_value_spike = {}
if setting_demands not in ["random","python_library"]:
    print("please run the script by python IBM_cplex_feasibiloty.py real/random1/random2 random/python_library")
else:
    storage_node_selection_schemes=["Degree","Random"]
    storage_node_selection_schemes=["Degree"]
    cyclic_workload = "sequential"
    storage_capacities = [800,1200,1500,2000]
    storage_capacities = [50,100,200,300,400,600,800,1000,1500,2000,4000,6000]
    storage_capacities = [12000]
    fidelity_threshold_ranges = [0.75,0.8,0.85,0.9,0.92,0.94,0.96,0.98]
    fidelity_threshold_ranges = [0.9,0.94]
    distance_between_users = 2

    given_life_time_set = [1000]# 1000 indicates infinite time slot life time and 2 indicates one time slot life
    
    number_of_time_slots = 10
    results_file_path = 'results/results_file_path.csv'
    inventory_utilization_results_file_path = 'results/inventory_utilization_results_file_path.csv'
    delived_purification_EPRs_file_path = 'results/delived_purification_EPRs_file_path.csv'
    each_network_topology_file = {}
    each_network_topology_file = {"SURFnet":'data/Surfnet'}
        
    each_topology_mean_value_spike={"SURFnet":[350]
                               }
feasibility(each_network_topology_file,results_file_path,inventory_utilization_results_file_path,delived_purification_EPRs_file_path,number_of_user_pairs,number_of_time_slots,spike_means,num_spikes,experiment_repeat,storage_node_selection_schemes,fidelity_threshold_ranges,cyclic_workload,storage_capacities,given_life_time_set,distance_between_users,setting_demands,edge_fidelity_ranges)









