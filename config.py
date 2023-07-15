class NetworkConfig(object):
  scale = 10
  pass

class Config(NetworkConfig):
  version = 'v1'

  project_name = 'QON'



  topology_file = 'SURFnet'
  traffic_file = 'WK1'
  test_traffic_file = 'WK2'
#   topology_file = 'ATT_topology_file_modified'
#   traffic_file = 'TM3'
#   test_traffic_file = 'TM4'
#   topology_file = 'test_topology'
#   traffic_file = 'TM'
#   test_traffic_file = 'TM2'
  time_intervals = 10

  max_moves = 30            #percentage
  

  # For pure policy
  baseline = 'avg'          #avg, best
  commitment_window_range = 8
  look_ahead_window_range = 10
  logging_training_epochs = True
  training_epochs_experiment = True
  printing_flag = False
  each_topology_each_t_each_f_paths= 'each_topology_each_t_each_f_paths.txt'
  testing_results = 'testing_results_final.csv'
  raeke_paths = "raeke_att.txt"
  raeke_paths = "raeke_abilene.txt"
  min_edge_capacity = 400
  max_edge_capacity = 1400
  min_edge_fidelity = 0.94
  max_edge_fidelity = 0.98
  fidelity_threshold = 0.7
  number_of_storages = 4
  delat_value = 20
  storage_capacity = 12000
  num_of_paths = 1
  path_selection_scheme = "shortest"
  cyclic_workload = True
  capacity_division = 1# 8 for att and 1 for abilene
  demand_scale = 4# 60 for att and 4 for abilene
def get_config(FLAGS):
  config = Config

  for k, v in FLAGS.__flags.items():
    if hasattr(config, k):
      setattr(config, k, v.value)

  return config
