 ###### Author: Mahboobe Rezaee #####

from __future__ import division

import os
import ast
import sys
import subprocess
import signal
import socket
import logging
import thread
import time
import tempfile
import math
import random
import networkx as nx
from collections import defaultdict, deque
from math import log
import sumolib
from k_shortest_paths import k_shortest_paths
from optparse import OptionParser
from bs4 import BeautifulSoup
from collections import defaultdict
#import simpla
from decimal import Decimal
from collections import deque
from heapq import heappush, heappop
from itertools import count
import networkx as nx
import xml.etree.ElementTree as ET
from networkx.utils import generate_unique_node
Dict_J_public = {}
Dict_edge_J = {}
dict_JJ_From = {}
dict_JJ_To = {}
J_list = []
listEdgeRSU = []
dict_road_conges_traffic_area={}
junction_dictionary ={}
 
TLS_List_xy={} 
TLS_List = []
junction_id =[]
lane_length = {}
lane_ITT = {}
lane_CTT = {}
lane_id=[]
avgLengthall=0
avgSpeedall=0
dict_edgeRSUs={}
dict_lane={}
laneallgraph=[]
edgeallgraph=[]
edgeallsgraph=[]
visit_bfs=[]
dict_fc={}
list_source={}
list_present_network=[]
list_vehicle_set_route=[]
number_of_lane={}
TMax=0
listcdm=[]

footprintList =[]
dict_footprint ={}
list_junctions2 = []
edgListLength =[]
edgListTT = []
# We need to import Python modules from the $SUMO_HOME/tools directory
if 'SUMO_HOME' in os.environ:
    tools = os.path.join(os.environ['SUMO_HOME'], 'tools')
    sys.path.append(tools)
else:
    sys.exit("Environment variable SUMO_HOME not defined")
    
import traci

class UnusedPortLock:
    lock = thread.allocate_lock()

    def __init__(self):
        self.acquired = False

    def __enter__(self):
        self.acquire()

    def __exit__(self):
        self.release()

    def acquire(self):
        if not self.acquired:
            UnusedPortLock.lock.acquire()
            self.acquired = True

    def release(self):
        if self.acquired:
            UnusedPortLock.lock.release()
            self.acquired = False

def find_unused_port():
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM, 0)
    sock.bind(('127.0.0.1', 0))
    sock.listen(socket.SOMAXCONN)
    ipaddr, port = sock.getsockname()
    sock.close()
    
    return port

def terminate_sumo(sumo):
    if sumo.returncode == None:
        os.kill(sumo.pid, signal.SIGTERM)
        time.sleep(0.5)
        if sumo.returncode == None:
            print (os.__file__)
            #os.kill(sumo.pid, signal.SIGKILL)
            time.sleep(1)
            if sumo.returncode == None:
                time.sleep(10)
    
	
def _dijkstra(G, source, get_weight, pred=None, paths=None, cutoff=None,
              target=None):
    
    G_succ = G.succ if G.is_directed() else G.adj

    push = heappush
    pop = heappop
    dist = {}  # dictionary of final distances
    seen = {source: 0}
    c = count()
    fringe = []  # use heapq with (distance,label) tuples
    push(fringe, (0, next(c), source))
    while fringe:
        (d, _, v) = pop(fringe)
        if v in dist:
            continue  # already searched this node.
        dist[v] = d
        if v == target:
            break

        for u, e in G_succ[v].items():
            cost = get_weight(v, u, e)
            if cost is None:
                continue
            vu_dist = dist[v] + get_weight(v, u, e)
            if cutoff is not None:
                if vu_dist > cutoff:
                    continue
            if u in dist:
                if vu_dist < dist[u]:
                    raise ValueError('Contradictory paths found:',
                                     'negative weights?')
            elif u not in seen or vu_dist < seen[u]:
                seen[u] = vu_dist
                push(fringe, (vu_dist, next(c), u))
                if paths is not None:
                    paths[u] = paths[v] + [u]
                if pred is not None:
                    pred[u] = [v]
            elif vu_dist == seen[u]:
                if pred is not None:
                    pred[u].append(v)

    if paths is not None:
        return (dist, paths)
    if pred is not None:
        return (pred, dist)
    return dist

def dijkstra_path(G, source, target, weight='weight'):
    
    (length, path) = single_source_dijkstra(G, source, target=target,
                                            weight=weight)
    try:
        return path[target]
    except KeyError:
        raise nx.NetworkXNoPath(
            "node %s not reachable from %s" % (source, target))#return (0)




def single_source_dijkstra(G, source, target=None, cutoff=None, weight='weight'):
    
    if source == target:
        return ({source: 0}, {source: [source]})

    if G.is_multigraph():
        get_weight = lambda u, v, data: min(
            eattr.get(weight, 1) for eattr in data.values())
    else:
        get_weight = lambda u, v, data: data.get(weight, 1)

    paths = {source: [source]}  # dictionary of paths
    return _dijkstra(G, source, get_weight, paths=paths, cutoff=cutoff,
                     target=target)


def dijkstra_path_length(G, source, target, weight='weight'):
    
    length = single_source_dijkstra_path_length(G, source, weight=weight)
    try:
        return length[target]
    except KeyError:
        return (0)

def single_source_dijkstra_path_length(G, source, cutoff=None,weight='weight'):
                                       
   
    if G.is_multigraph():
        get_weight = lambda u, v, data: min(
            eattr.get(weight, 1) for eattr in data.values())
    else:
        get_weight = lambda u, v, data: data.get(weight, 1)

    return _dijkstra(G, source, get_weight, cutoff=cutoff)

   
def update_travel_time_on_roads(graph, time):
    for road in graph.nodes_iter():
         
        logging.debug("roadroadroadroad : %s" % road )
        for successor_road in graph.successors_iter(road):
                logging.debug("successor_road : %s" % successor_road )
                maxLenght = max(edgListLength)
                if road in listEdgeRSU:
				 graph.edge[road][successor_road]["weight1"] = (graph.edge[road][successor_road]["length"] / maxLenght)+ dict_road_conges_traffic_area[road]
                else:
				  graph.edge[road][successor_road]["weight1"] = (graph.edge[road][successor_road]["length"] / maxLenght)#+ dict_road_conges_traffic_area[road]
                 
     
def Road_RSU_congestion_index(edgelist,rsuid, net):####################################################3
          #for rsuid in RSU_ids:
			 list_of_vehicle=[]
			 congestedRoads=[]
			 vehiclecongested=[]
			 Sum_Zone_RSUs={}
			 Sum_Zone=0
			 Sum_Lane_L=0
			 Sum_Lane_WedgeZ=0
			 # maxLenght = max(edgListLength)
			 # max_speed = max(edgListspeed)
			 for edge in edgelist[rsuid]:
				  # logging.debug("edgelist (%s, %s)" % (rsuid, edge))
				  lanelen = traci.lane.getLength(edge + '_' + '0')
				  Max_speed_LaneZ = traci.lane.getMaxSpeed(edge + '_' + '0')
				  MeanSpeedZ= traci.edge.getLastStepMeanSpeed(edge)

				  edge_road = net.getEdge(edge)
				  N_Lane = edge_road.getLaneNumber()
				  logging.debug("N_Lane[edge]::::(%s)" % (N_Lane))
				  Kjam = float ((lanelen * N_Lane)/ (7.5))
				  
                  
     
				  number_vehicles = traci.edge.getLastStepVehicleNumber(edge)
				  Wedgev = 1 - (MeanSpeedZ / Max_speed_LaneZ)
				  Wedgek = float(number_vehicles / Kjam)
				  WedgeZ = float((Wedgev + Wedgek) / (2))
				  #logging.debug("WedgeZ:::::::: %s" % WedgeZ)
				   #w += wlane # for each lane
				  Sum_Lane_L += lanelen 
				  Sum_Lane_WedgeZ  += lanelen * WedgeZ
				  # logging.debug("Sum_Lane_WedgeZ : %s" % Sum_Lane_WedgeZ )
				  # logging.debug("sum_lane_len : %s" % Sum_Lane_L )
				  #logging.debug("j: %s" % f)
				  #s=traci.edge.getLastStepVehicleNumber(edge)
				  #logging.debug("getLastStepVehicleNumber: %s" % s)
				 
			 Sum_Zone = float(Sum_Lane_WedgeZ  / Sum_Lane_L )
			 logging.debug("Sum_ZoneSum_Zone: (%s, %s)" % (Sum_Zone, rsuid))
			 return float(Sum_Zone)
def road_congestion_at_traffic_area(road_graph_travel_time, edgelist, zone_conges, RSU_ids,net):					
  for rsuid in RSU_ids:
	for edge in edgelist[rsuid]:
	   listEdgeRSU.append(edge)
	   Lenght_Lane = traci.lane.getLength(edge + '_' + '0')
	   Max_speed_LaneZ = traci.lane.getMaxSpeed(edge + '_' + '0')
	   MeanSpeedZ= traci.edge.getLastStepMeanSpeed(edge)
	   edge_road = net.getEdge(edge)
	   N_Lane = edge_road.getLaneNumber()
	   logging.debug("N_Lane[edge]::::(%s)" % (N_Lane))
	   Kjam = float ((Lenght_Lane * N_Lane)/ (7.5))
	   number_vehicles = traci.edge.getLastStepVehicleNumber(edge)
	   Wedgev = 1 - (MeanSpeedZ / Max_speed_LaneZ)
	   #Wedgek = float(number_vehicles / Kjam)
	   if number_vehicles !=0 and Lenght_Lane >= 9:
	     Density = float (number_vehicles / Kjam)
	   else:
	     Density = 0.0

	   ZoneC = zone_conges[rsuid]
	   sum_conges= (Wedgev+ (4 *ZoneC)+Density)/6
	   dict_road_conges_traffic_area[edge] = sum_conges
	   

def build_road_graph(network):                
    # Input   
    f = open(network, 'r')
    data = f.read()
    soup = BeautifulSoup(data)
    f.close()
	
	
    edges_length={}
    for edge_tag in soup.findAll("edge"):
        lane_tag = edge_tag.find("lane")
        
        edge_id = edge_tag["id"]
        edge_length = int(float(lane_tag["length"]))
        
        edges_length[edge_id] = edge_length
        # lane_tag = edge_tag.find("lane")
        # edge_length = float(lane_tag["length"])
        # edges_length[edge_id] = edge_length
        # edgListLength.append(edge_length)
    
    graph = nx.DiGraph()            
    
    for connection_tag in soup.findAll("connection"):
        source_edge = connection_tag["from"]        
        dest_edge = connection_tag["to"]
       
		
	graph.add_edge(source_edge.encode("ascii"), dest_edge.encode("ascii"), length=edges_length[source_edge], weight1=0, weight2= 0)
	print("source= {0}    dest= {1}   length= {2}     weight1= 0 weight2= 0" .format(source_edge.encode("ascii"),dest_edge.encode("ascii"),edges_length[source_edge]))
        print("\t\t\t")
    return graph
	
 
def build_road_graph_Lane(network, net):                
    logging.debug("build_road_graph0")   
    f = open("D:\\E\\d\\sumo-0.25.0\\bin\\los.net.xml", 'r')
    data = f.read()
    soup = BeautifulSoup(data)
    f.close()
    sys.stdout = open('RSU.txt','wt')
    #number_of_lane = defaultdict(lambda: 0, number_of_lane)
    edges_length={}
    edge_from ={}
    edge_to ={}
    numberlane = {}
    mul=0
    for edge_tag in soup.findAll("edge"):
	  edge_id = edge_tag["id"]
	  # logging.debug("Typeedge_id::::(%s)" % (type(edge_id)))
	  lane_tag = edge_tag.find("lane")
	  #numberlane[edge_id]=0
	  # for lane in lane_tag:
	   # numberlane[edge_id] = numberlane[edge_id] + 1
	  edge_length = float(lane_tag["length"])
	  edge_speed = float(lane_tag["speed"])
	  edges_length[edge_id] = edge_length
	  # mul = float (numberlane[edge_id] * edge_length)
	  edgListLength.append(edge_length)
	  edgListTT.append((edge_length/edge_speed))
	  
	  edgeallsgraph.append(edge_id)
	  lane_tagall= edge_tag.findAll("lane")
	  laneid=[]
	  number_of_lane[edge_id]=0
	  for lane in lane_tagall:
	   laneid.append(lane["id"])
	   laneallgraph.append(lane["id"])
	   dict_lane[edge_id]= laneid
	   number_of_lane[edge_id]= number_of_lane[edge_id] + 1
    #maxLenght = max(edgListLength)
    
   
        
	    
        # lane_tag = edge_tag.find("lane")
		
	
	# print(lane_tagall)
	
	
	# print("edge_id:{0}".format(edge_id)) 
	# laneid=[]
	# for lane in lane_tagall:
	 # laneid.append(lane["id"]) 
	 # laneallgraph.append(lane["id"])
	 # dict_lane[edge_id]= laneid
	# # print("dict_lane[{0}] = {1}".format(edge_id,dict_lane[edge_id])) 
        
    graphlane = nx.DiGraph() 
    # for edge_tag in soup.findAll("edge"):
	  # edge_id = edge_tag["id"]
	  # lane_tag = edge_tag.find("lane")
	  # edge_length = int(float(lane_tag["length"]))
	  # if edge_id.startswith(":"): continue
	  # #edge_id = net.getEdge(edge_id)
	  # edge_from =  net.getEdge(edge_id).getFromNode().getID()
	  # edge_to =  net.getEdge(edge_id).getToNode().getID()
	  # FromNodeC = net.getNode(edge_from).getCoord()
	  # ToNodeC = net.getNode(edge_to).getCoord()
    for edg_tag in soup.findAll("edge"):
	 edg_id = edg_tag["id"]
	 #tonode= edg_tag["to"]
	 if edg_id.startswith(":") : continue
	 edgeallgraph.append(edg_id)
	 #tonodedict[edg_id]= tonode
    
    for junction_tag in soup.findAll("junction"):
	 junction_id = junction_tag["id"]
	 list_junctions2.append(junction_id) 
	 junction_x = junction_tag["x"]
	 junction_y = junction_tag["y"]
	 junction_dictionary[junction_id] = (junction_x, junction_y)
    for J in list_junctions2:
	 edge_J_list = []
	 for edge_tag in soup.findAll("edge"):
	  edge_id = edge_tag["id"]
	  lane_tag = edge_tag.find("lane")
	  edge_length = int(float(lane_tag["length"]))
	  if edge_id.startswith(":"): continue
	  #edge_id = net.getEdge(edge_id)
	  edge_from[edge_id] =  net.getEdge(edge_id).getFromNode().getID()
	  edge_to[edge_id] =  net.getEdge(edge_id).getToNode().getID()
	  # if J == edge_from :
	   # edge_J_list.append(edge_id)
	  # if J == edge_to :
	   # edge_J_list.append(edge_id)
     # Dict_J_public[J] = edge_J_list
	 
    
	
    
    for connection_tag in soup.findAll("connection"):
        source_edge = connection_tag["from"]        
        dest_edge = connection_tag["to"]
        if source_edge.startswith(":") or dest_edge.startswith(":"):
		 graphlane.add_edge(source_edge.encode("ascii"), dest_edge.encode("ascii"), edge_From =0, edge_To =0, length=edges_length[source_edge], TTg=0, weight=0 , TT=0, Counter=0)
		 # print("source= {0}    dest= {1}    length= {2}   TTg=0  weight= 0  predict=0 TT=0 Counter=0" .format(source_edge.encode("ascii"),dest_edge.encode("ascii"),edges_length[source_edge]))

        else:
         edge_net = net.getEdge(source_edge)
         nextEdge = net.getEdge(dest_edge)
         connection = str(edge_net.getOutgoing()[nextEdge][0])       
         FromLane = connection.split(' ')[3]
		 
         s,fromLane = FromLane.split("fromLane=")
         logging.debug("connection::::(%s)" % (connection))
         logging.debug("FromLaneFromLaneFromLane::::(%s)" % (fromLane))
         ToLane = connection.split(' ')[4]
         s,toLane = ToLane.split("toLane=")
         logging.debug("ToLaneToLane::::(%s)" % (toLane))
         #TLS = edge_net.getTLS()
         source_edge_lane = source_edge+"_"+ast.literal_eval(fromLane)
         dest_edge_lane = dest_edge+"_"+ast.literal_eval(toLane) 
         logging.debug("graphlane") 
         graphlane.add_edge(source_edge_lane.encode("ascii"), dest_edge_lane.encode("ascii"), edge_From = edge_from[source_edge], edge_To = edge_to[source_edge], length= edges_length[source_edge], FLane = fromLane, TLane = toLane, TTg=0, weight=0 ,predict=0, TT=0, Counter=0)
         # print("source= {0}    dest= {1}    length= {2}  FLane={3}   TLane={4} TTg=0 weight= 0  predict=0 TT=0 Counter=0" .format(source_edge.encode("ascii"),dest_edge.encode("ascii"),edges_length[source_edge] , fromLane, toLane))
        # print("\t\t\t")
    
    return graphlane


def bfs_edges(G, source, reverse=False, L=0):
    if reverse :#and isinstance(G, nx.DiGraph):
        neighbors = G.predecessors_iter
    else:
        neighbors = G.successors_iter
        #print ("neighbors::: {0}" .format(neighbors))
    visited = set([source])
    del visit_bfs[:]
    visit_bfs.append(source)
    queue = deque([(source, neighbors(source), 0)])
    
    #qqueue = queue
    
    while queue:# and qqueue:
        parent, children, v = queue[0]
        q= children
        #print ("parent::: {0}" .format(parent ))
        #print ("children::: {0}" .format(children ))
        front= queue.popleft()
        #print ("front::: {0}" .format(front ))
        level = front[2]
        #print ("level::: {0}" .format(level ))
        if level >= L:
		      break
        level +=1
        
        for child in children:#while next(q):
            #child = next(children)
            #print ("child::: {0}" .format(child))
            
            if child not in visited:
                yield parent, child
                visited.add(child)
                visit_bfs.append(child)
                queue.append((child, neighbors(child), level))
	





def numberv(l):
    nb = 0
    shape = traci.lane.getShape(l)
    X,Y = shape[-1]
    for k in traci.lane.getLastStepVehicleIDs(l):
        if traci.vehicle.getLanePosition(k) < X-100:
             nb += 1
    return nb

		
             
		
def run(network, begin, end, interval):###############################
   
    
    logging.debug("sumolib.net.readNet") 
    net = sumolib.net.readNet("D:\\E\\d\\sumo-0.25.0\\bin\\los.net.xml")
    road_graph = build_road_graph("D:\\E\\d\\sumo-0.25.0\\bin\\los.net.xml")
    lane_graph = build_road_graph_Lane("D:\\E\\d\\sumo-0.25.0\\bin\\los.net.xml", net)
    logging.debug("Building Lane  complete graph")
	
    buffered_paths = {}	
    list_of_vehicle=[]
    subgraph_g={}
    dicttt_edgeRSUs={}
    f = open('RSUsLocationUBC1.xml', 'r')
    data = f.read()
    soup = BeautifulSoup(data)
    f.close()
    RSU_ids=[]
    RSU_x={}
    RSU_y={}
    edgelist={}
    closestEdge=[]
    edg_ids=[]
    listalledge=[]

    
    for RSU_tag in soup.findAll("poly"):
     
      RSU_id = RSU_tag["id"]
      RSU_ids.append(RSU_id)
      RSU_center = RSU_tag["center"]
      RSU_x[RSU_id], RSU_y[RSU_id] = RSU_center.split(",")
	
      x =float(RSU_x[RSU_id])
      y =float(RSU_y[RSU_id])
      # logging.debug("Set of edges within the reach of each RSU")
      list_EdgeId=[]
      list_NormalEdges=[]
      list_junctions=[]
      
      edges = net.getNeighboringEdges(x, y, 500)
      for ege in edges:
	    closestEdge , dist = ege
	    #print ("{0} closestEdge= {1}" .format(RSU_id ,closestEdge ))
	    list_NormalEdges.append(str(closestEdge))
	    #print ("{0} list_NormalEdges= {1}" .format(RSU_id ,list_NormalEdges ))
	    
	    data = list_NormalEdges[0].split('id=')[1]
	    EdgeId = data.split(' ')[0]
	    
	    
		
           
	    listalledge.append(ast.literal_eval(EdgeId))
	    list_EdgeId.append(ast.literal_eval(EdgeId))
	    #########################################
	  # print("{0} list_EdgeId= {1}" .format(RSU_id ,list_EdgeId ))##########################
	  
          # JunctionFrom = data.split('from=')[1]
	  # JunctionFrom = JunctionFrom.split(' ')[0]
       	  # list_junctions.append(ast.literal_eval(JunctionFrom))
          # JunctionTo = data.split('to=')[-1]
          # JunctionTo = JunctionTo.split('/>')[0]
          # list_junctions.append(ast.literal_eval(JunctionTo))
	    del list_NormalEdges[:]# : means all memebers
      # print ("{0} list_junctions:::: {1}" .format(RSU_id ,list_junctions ))
	  # ############################################################################################
      # subgraph_g[RSU_tag]=road_graph_travel_time.subgraph(list_junctions)
	  # ############################################################################################
      # print ("{0} graph_list_junctions:::: {1}" .format(RSU_id ,subgraph_g[RSU_tag].nodes() ))
	  # ############################################################################################
      #subgraph_g[RSU_id]=road_graph_travel_time.subgraph(list_EdgeId)## SUBGRAPH  SUBGRAPH   SUBGRAPH   SUBGRAPH  ##
	  ##############################################################################################
      # print ("{0} graph_list_EdgeIdedge:::: {1}" .format(RSU_id ,   subgraph_g[RSU_id].edges() ))
	  
      dicttt_edgeRSUs[RSU_id]=list_EdgeId
      
      # print ("{0} dict_edgeRSUs:::: {1}" .format(RSU_id ,dicttt_edgeRSUs[RSU_id] ))
      edgelist[RSU_id]= list_EdgeId
      # logging.debug("edgelist[RSU_id]edgelist[%s]:%s " % (RSU_id,edgelist[RSU_id]))
      # print ("{0} edgelist:::: {1}" .format(RSU_id ,edgelist[RSU_id] ))

      # del list_EdgeId[:]
      # del list_junctions[:]
      del list_NormalEdges[:]
    # logging.debug("Finding all simple paths")
    
    # Used to enhance performance only
    buffered_paths = {}
    
    # logging.debug("Running simulation now")    
    step = 1
    # The time at which the first re-routing will happen
    rerouting_step = begin #800
    # The time at which a cycle for collecting travel time measurements begins
    travel_time_cycle_begin = interval  #600
    duration = 200
    duration2=200
    beginp = 0
    endp = 1
    periodic  = 1
    # logging.debug("stepstepstepstepstepstep: %d" % step)
    #dict_edge_ave_speed
    zone_conges={}
    lengthSum = 0.0
    edgeCount=0
    sum_speed_net=0
    #traci.vehicle.setStop("t", "-40114658#1", 1, 0)
    # for edge in edgeallgraph:
		     # sum_speed_net += traci.lane.getMaxSpeed(edge + '_' + '0')
		     # lengthSum += traci.lane.getLength(edge + '_' + '0')
                     
		     # edgeCount += 1		 
			 
    # logging.debug("lengthSum: %d" % lengthSum)
    # logging.debug("edgeCount: %d" % edgeCount)
    # avgLengthall = lengthSum / edgeCount
    # # logging.debug("avgLengthallavgLengthall: %d" % avgLengthall)
    # avgSpeedall = sum_speed_net / edgeCount
    # # logging.debug("sum_speed_net: %d" % sum_speed_net)
    # logging.debug("avgSpeedallavgSpeedall: %d" % avgSpeedall)
    #sys.stdout = open('TestAll.txt','wt')
    
   
    logging.debug("simulationStep0:: " )
    periodic2  = 1
    for J in list_junctions2:
      list_JJ_From = []
      list_JJ_To = []
      for road in lane_graph.nodes_iter():
	    for successor_road in lane_graph.successors_iter(road):
		   if J == lane_graph.edge[road][successor_road]['edge_From']:
		    list_JJ_From.append( road )
		   if J == lane_graph.edge[road][successor_road]['edge_To']:
		    list_JJ_To.append( road )
      dict_JJ_From[J]=  list_JJ_From    
      dict_JJ_To[J]=  list_JJ_To 
    maxTT = max(edgListTT) 
    while step == 1 or traci.simulation.getMinExpectedNumber() > 0:
        traci.simulationStep()
        logging.debug("simulationStep1::  %s" % traci.simulationStep() )
        detect_vehicle_in_RSU_other=[]
        if periodic >=100 and periodic <= end and periodic%duration==0:
		   logging.debug("Simulation Step for Zone: %d" % step)
		   for rsuid in RSU_ids:
		    if len(edgelist[rsuid]) > 0:
			 logging.debug("rsuid for zone_conges start %s" % rsuid)
			 logging.debug("rsuid edgelist[%s]  %s" % (rsuid,edgelist[rsuid]))
			 zone_conges[rsuid] = float(Road_RSU_congestion_index(edgelist, rsuid, net))
			 subgraph_gg=road_graph.subgraph(dicttt_edgeRSUs[rsuid])
			 #prediction_area_RSU(subgraph_gg,road_graph_travel_time, edgelist,rsuid, net)
			
			 
        if step >= travel_time_cycle_begin and travel_time_cycle_begin <= end and step%interval == 0:
            periodic  = 1
            # logging.debug("Updating travel time on roads at simulation time %d" % step)
            list_present_network=[]
			################ Update Travel Time ##############################
            print("first")
            #travel_time_on_roads(road_graph, step, travel_time_cycle_begin == step)
            #prediction_on_edge(road_graph_travel_time, net)
            road_congestion_at_traffic_area(road_graph, edgelist, zone_conges, RSU_ids,net)
            update_travel_time_on_roads(road_graph, time)
            #Update_Travel_Time(road_graph_travel_time, net)
            for edge in edgeallgraph:
			  dict_footprint[edge]=0
            #del footprintList[:]
            #dict_footprint.clear()
            #i=0
           
   
			
	    congestedRoadsss=[]
	    for edge in edgeallgraph:
		 #for lanelist in dict_lane[edge]:
		    #for lane in lanelist:
			   listspeedss=[]
			   listvss=[]
			   Max_speed_LaneC = traci.lane.getMaxSpeed(edge + '_' + '0')# Get Maximum Allowed speed
			   listvss.append(traci.edge.getLastStepVehicleIDs(edge))
			   MeanSpeeds= traci.edge.getLastStepMeanSpeed(edge)
			   # logging.debug("getLastStepMeanSpeed: %s" % MeanSpeeds)
			   sumspeedss=0
			   averagespeedss=0
			   jjj=0
			   wwwedge=0
			   listvehicless=[]
			   vehiclecongestedss=[]
			   # for vv in listvss:
				# for v in vv:
					# listvehicless.append(v)
					# #logging.debug("listvehicle: %s" % listvehicless)
					
			   # if len(listvehicless)!= 0: 
				# for vid in listvehicless: 
					 # logging.debug("vid in vehicle: %s" % vid)
					 # listspeedss.append(traci.vehicle.getSpeed(vid))
					 # sumspeedss += traci.vehicle.getSpeed(vid)
					 # logging.debug("traci.vehicle.getSpeed(vid): %s" % traci.vehicle.getSpeed(vid))
					 # jjj+=1
			   # if jjj>0 and listspeedss is not None :
					   # logging.debug("listspeedmax : %s" % listspeedss)
					   # maxspeedss = max(listspeedss) # V_max
					   # logging.debug("maxspeed: %s" % max_speed_Lane)
					   # logging.debug("j: %s" % jjj)
					   
					   # averagespeedss = sumspeedss / jjj# V_ave
					   # logging.debug("averagespeed: %s" % averagespeedss)
			   # if averagespeedss!=0:
			   Wedge_cloud = 1-(MeanSpeeds / Max_speed_LaneC)
			   logging.debug("Wedge_cloud: %s" % Wedge_cloud)
			   if Wedge_cloud >=0.5:
				 congestedRoadsss.append(edge)
		#############################################  select vehicle for rerouting by cloud server  #######################################	   
	    list_of_vehiclecloud=[]
            
	    for edge in edgeallgraph:
		     
		     if edge in listalledge:continue
		
		     list_of_vehiclecloud.append(traci.edge.getLastStepVehicleIDs(edge))
             
			 
			 
            			
 	    # if len(congestedRoadsss) != 0 :
			# logging.debug("cloud_reroute_vehicles is staaaaaaaaaaaaaaaaaaaaaaaart: " )  
			# #cloud_reroute_vehicles(road_graph_travel_time,list_of_vehiclecloud,congestedRoadsss,buffered_paths, list_present_network, travel_time_cycle_begin == step, net)
			# logging.debug("cloud_reroute_vehicles is eeeeeeeeeeeeeeeeeeeeeeeeeend: " )
	#########################################################################################################################################		
		#######################################################  Re-Routing for each RSU ################################################
            for rsuid in RSU_ids:
			 subgraph_g[rsuid]=road_graph.subgraph(dicttt_edgeRSUs[rsuid])
			 list_of_vehicle=[]
			 congestedRoads=[]
			 vehiclecongested=[]
			 list_present=[]
			 if len(edgelist[rsuid])== 0:continue
			 logging.debug("len(edgelist[rsuid]) is not none %s" % rsuid)
			 for edge in edgelist[rsuid]:
				   del visit_bfs[:]
				   logging.debug("edgelist (%s, %s)" % (rsuid, edge))
				  #print ("lane in edge{0} = {1}" .format(edgee ,dict_lane[edge] ))
				  #for lane in dict_lane[edge]:
                                  # logging.debug("Simulation for RSU%d -> dict_lane[%s] = lane %s" % (i , edge, lane))
                    
				   #listspeed=[]
				   MeanSpeed=0.0
				   number_vehicle=0
				   
				   
				   max_speed_Lane = float(traci.lane.getMaxSpeed(edge + '_' + '0'))# Get Maximum Allowed speed
				   Lenght_Lane = float(traci.lane.getLength(edge + '_' + '0'))
				   # logging.debug("Lenght_Lane: %s" % Lenght_Lane)
				   LastStepLength = float(traci.edge.getLastStepLength(edge))
				   # logging.debug("LastStepLength: %s" % LastStepLength)
				   listv=traci.edge.getLastStepVehicleIDs(edge) # Get the all vehicle in lane
				   # number_vehicle = traci.edge.getLastStepVehicleNumber(edge)
				   # logging.debug("number_vehicle: %s" % number_vehicle)
				   # logging.debug("listvvvvvv: %s" % listv)
				   MeanSpeed= float(traci.edge.getLastStepMeanSpeed(edge))
				   Wedge = float(1 - (MeanSpeed / max_speed_Lane))
				   # logging.debug("Wedge: %s" % Wedge)
				   Denc=0
				   edge_road = net.getEdge(edge)
				   N_Lane = edge_road.getLaneNumber()
				   number_vehicles =(traci.edge.getLastStepVehicleNumber(edge))
				   Kjam = float ((Lenght_Lane * N_Lane)/ (7.5))
				   if number_vehicles !=0 and Lenght_Lane >= 9:
				    
				    Density = float (number_vehicles / Kjam)
				   else:
				    Density = 0.0
				    
				   
				   ZoneC = zone_conges[rsuid]
				  
				   sum_conges= (Wedge+ZoneC+Density)/3
				   listcdm.append(sum_conges)
				   if ZoneC >=0.5:
				    sum_conges= (Wedge+ZoneC+Density)/3
				   else:
				    sum_conges= ( Wedge + Density )/2
				   print("roadtest: {0}".format(edge))
				   print ("{0}w3 id={1}{2}{3} {4}{5}" .format('<','"',sum_conges,'"','/','>'))
				   logging.debug("Ki/Kjam::::::  %s" % Density )
				   logging.debug("Kjam::::::  %s" % Kjam )
				   logging.debug("1-V/Vmax::::::::::::::  %s" % Wedge )
				   logging.debug("RSU's ZONE::::::: %s" % ZoneC)
				   logging.debug("CDM_W3:::::::: %s" % sum_conges)
				   logging.debug("number_vehicles::::::  %d" % number_vehicles )
				   
				   if  sum_conges >= 0.5:#((sum_conges + ZoneC)/ 2) >= 0.8:#Density >= 0.5: # sum_conges >= 0.5:# (Wedge+Density)/2 >= 0.5: # ((sum_conges + ZoneC)/ 2) >= 0.5: 
				        print(list(bfs_edges(subgraph_g[rsuid], edge, reverse=True, L=3)))
				        congestedRoads.append(edge)
				        # logging.debug("visit_bfs: %s" % visit_bfs)
				        for v in visit_bfs:
				            if v in list_present: continue
				            #if v in list_present: continue
				            list_present.append(v)
				            if v.startswith(":"): continue
				            vehiclecongested.append(traci.edge.getLastStepVehicleIDs(v))
				        
				   if len(detect_vehicle_in_RSU_other)!= 0:
				      for vv in vehiclecongested:
				        for v in vv:
						  if v not in detect_vehicle_in_RSU_other:
						   list_of_vehicle.append(v)
						   # logging.debug("listvehicle: %s" % list_of_vehicle)
						   detect_vehicle_in_RSU_other.append(v)
						   # logging.debug("detect_vehicle_in_RSU_other: %s" % detect_vehicle_in_RSU_other)
					        
							
				   else:
				      for vv in vehiclecongested:
				        for v in vv:
						  list_of_vehicle.append(v)
						  # logging.debug("listvehicle: %s" % list_of_vehicle)
						  detect_vehicle_in_RSU_other.append(v)
						  # logging.debug("detect_vehicle_in_RSU_other: %s" % detect_vehicle_in_RSU_other)
                     				  
				   
				         
			 for v in list_of_vehicle:
			  pos_lane = traci.vehicle.getLaneID(v)
			  pos_edge = traci.vehicle.getRoadID(v)
			  route = traci.vehicle.getRoute(v)
			  destination = route[-1]
			  if pos_edge == destination:continue
			  if pos_edge == destination:continue
			  next_road = (route.index(pos_edge)) + 1
			  if route[next_road] == destination: continue
			  edge_dest =  net.getEdge(destination).getToNode().getID()
			  # destNodeC = net.getNode(edge_dest).getCoord()
			  # x_dest, y_dest = destNodeC
			  #sqrtxy = math.sqrt((x_dest - x_road)* (x_dest - x_road)) + ((y_dest - y_road) * (y_dest - y_road))
			  # Di[road] = Lenght_Lane + math.sqrt(sqrtxy)
			  # Di_list.append(Di[road])
			  edge_id = traci.lane.getEdgeID(pos_lane)
			  junction_ID =  net.getEdge(edge_id).getToNode().getID()
			  if len(dict_JJ_To[junction_ID]) >=2:
			   for lane in dict_JJ_To[junction_ID]:
			    
				edge_id1 = traci.lane.getEdgeID(lane)
				Cap = (5+2.5) / traci.lane.getLength(lane)
				# roadNodeC = net.getNode(edge_id1).getCoord()
				# x_road, y_road = roadNodeC
				Length_lane = traci.lane.getLength(lane)
				Speed_lane = traci.lane.getMaxSpeed(lane)
				length_Queue = numberv(lane)
				Number_Vehicles = traci.lane.getLastStepVehicleNumber(lane)
				TT = ((Length_lane - length_Queue)/(Speed_lane * (1-((Number_Vehicles * 7.5) /Length_lane) )))
				edge_net = net.getEdge(edge_id1)
				TLS = edge_net.getTLS()
				print(list(bfs_edges(road_graph, edge_id1, reverse=False, L= 1)))
				dict_numVehicle_for_next_road={}
				for ed in edgeallgraph:
				 dict_numVehicle_for_next_road[ed] = 0
				Q_i_out=0
				Q_i_Per = 0
				Vehicle_ids= traci.edge.getLastStepVehicleIDs(edge_id1)
				for edge in visit_bfs:
				 if edge==edge_id1:continue 
				 
				 for edge in visit_bfs:
				  if edge==edge_id1:continue
				  if dict_footprint[edge] > 0:
				   dict_numVehicle_for_next_road[edge] = dict_footprint[edge]
				  else:
				   for  v in Vehicle_ids:
				    
					route= traci.vehicle.getRoute(v)
					currentpos = traci.vehicle.getRoadID(v)
					if currentpos != route[-1]:
					 next_road= (route.index(currentpos)) + 1
					 if route[next_road] in visit_bfs:
					  dict_numVehicle_for_next_road[route[next_road]] += 1
				  
				 for edge in visit_bfs:
				  if edge==edge_id1:continue
				  if dict_numVehicle_for_next_road[edge] != 0:
				   timeTT = edge_net.getLength() / edge_net.getSpeed()
				   
				   if TLS is not None:
				    
					TLSID = TLS.getID()
					links = traci.trafficlights.getControlledLinks(TLSID)
					state = traci.trafficlights.getRedYellowGreenState(TLSID)
					dict_State ={}
					i = 0
					for sta in state:
					 dict_State[i] = sta
					 i += 1
					logging.debug("edge_id1: %s" % edge_id1)
					logging.debug("edge: %s" % edge)
					has = lane_graph.has_edge(edge_id1,edge) 
					if has == 'True':
					 flane = lane_graph.edge[edge_id1][edge]["FLane"]
					 logging.debug("flane: %s" % flane)
					 tlane = lane_graph.edge[edge_id1][edge]["TLane"] 
				  	 logging.debug("tlane: %s" % tlane)
					 for conn in links:
					  indicate = links.index(conn)
					  logging.debug("indicate: %s" % indicate)
					  if (edge_id1 + '_' + flane) == conn[0]:
					   if (edge + '_' + tlane) == conn[1]:
					    if dict_State[indicate] == 'G':
					     Duration = traci.trafficlights.getPhaseDuration(TLSID)
					     Q_i_out += dict_numVehicle_for_next_road[edge]  *  (Duration / 90) * (1/timeTT)
					else:
					 Q_i_out += 0
					 
                     
				   else:
					   
						Q_i_out += dict_numVehicle_for_next_road[edge]  *   (1/timeTT) 
                   
				  else:
				   Q_i_out += 0
				  
                 
				print(list(bfs_edges(road_graph, edge_id1, reverse=True, L= 1)))
				for edge in visit_bfs:
				  if edge==edge_id1:continue 
				  if dict_footprint[edge] !=0:
				   edge_net = net.getEdge(edge_id1)
				   timeTT = edge_net.getLength() / edge_net.getSpeed()
				   TLS = edge_net.getTLS()
				   if TLS is not None:
				    
					TLSID = TLS.getID()
					state = traci.trafficlights.getRedYellowGreenState(TLSID)
					dict_State ={}
					i = 0
					for sta in state:
					 dict_State[i] = sta
					 i += 1
					has = lane_graph.has_edge(edge,edge_id1) 
					if has == 'True':
					 flane = lane_graph.edge[edge][edge_id1]["FLane"]
					 tlane = lane_graph.edge[edge][edge_id1]["TLane"]
					 for conn in links:
					  indicate = links.index(conn)
					  if (edge + '_' + flane) == conn[0]:
					   if (edge_id1 + '_' + tlane) == conn[1]:
					    if dict_State[indicate] == 'G':
					    
						 Duration = traci.trafficlights.getPhaseDuration(TLSID)
						 Q_i_Per += dict_footprint[edge]  *  (Duration / 90) * (1/timeTT)
					 
					else:
					 Q_i_Per += 0
					 
				   else:
				    Q_i_Per += dict_footprint[edge]  *  (1/timeTT) 
				    
				  else:
				   Q_i_Per += 0
				  
		
				print(list(bfs_edges(road_graph, pos_edge, reverse=False, L= 3)))
				routetoD =dijkstra_path(road_graph, edge, destination, "weight1" )
				conges =[]
				Weight_Lane={}
				routeSD={}
				for lane in dict_JJ_To[junction_ID]:
				 Weight_Lane[lane] = 'none'
				for r in visit_bfs:
				   if r in congestedRoads:
				    conges.append(r)
				for r in routetoD:
				  if r in conges:
				    Weight_Lane[lane] = 'none'
				  else:
				    
					Weight_Lane[lane] = (TT/maxTT) + ((Number_Vehicles - Q_i_out + Q_i_Per) / Cap) + dijkstra_path_length(road_graph, edge, destination, "weight1" ) 
					routeSD[lane] = routetoD
                    
				   
				  
                  
                  
                  
                  
              
          
				min_weight=0
				for lane in dict_JJ_To[junction_ID]:
				  if min_weight ==0:
				   if Weight_Lane[lane] != 'none':
				    
					min_weight = Weight_Lane[lane]
					min_lane = traci.lane.getEdgeID(lane)
					# minlistlan =[]
					# minlistlan.append(min_lane)
					 
					
					
				    
                    
                    
                    
                    
				  else:
				   if Weight_Lane[lane] != 'none':
				    
					min_weight = Weight_Lane[lane]
					min_lane = traci.lane.getEdgeID(lane)
				  if min_weight !=0:
				   route = traci.vehicle.getRoute(v)
				   source = traci.vehicle.getRoadID(v)
				   logging.debug("route::::::::::::::  %s" % route)
				   logging.debug("source::::::::::::::  %s" % source)
				   new_route = []
				   new_route=route[0:route.index(source)] 
				   logging.debug("new_routemin_lanepos_edge::::::::::::::  %s" % new_route)
				   minlistlan =[]
				   minlistlan.append(source)
				   minlistlan.append(min_lane)
				   logging.debug("new_routemin_lanepos_edge::::::::::::::  %s" % minlistlan)
				   new_route += minlistlan
				   logging.debug("new_routemin_lanepos_edge::::::::::::::  %s" % new_route)
				   logging.debug("new_routemin_lane::::::::::::::  %s" % min_lane)
				   new_route += routeSD[lane]
				   logging.debug("new_route::::::::::::::  %s" % new_route)
				   traci.vehicle.setRoute(v, new_route)
				  else:
				   traci.vehicle.setRoute(v, route)
				  
				
		     
            rerouting_step += interval
            #beginp += interval
            travel_time_cycle_begin = step + 1
        step += 1 
        periodic +=1
        
   
    # logging.debug("max(CDM)::::::::::::::  %s" % max(listcdm))
    # logging.debug("min(CDM)::::::::::::::  %s" % min(listcdm))
    # logging.debug("max(TravelTime)::::::::::::::  %s" % max(listtraveltime))
    # logging.debug("min(TravelTime)::::::::::::::  %s" % min(listtraveltime))
    # logging.debug("max(list_predict)::::::::::::::  %s" % max(list_predict))
    # logging.debug("min(list_predict)::::::::::::::  %s" % min(list_predict))

    # logging.debug("max(NormalTravelTime)::::::::::::::  %s" % max(listNtraveltime))
    # logging.debug("max(NormalTravelTime)::::::::::::::  %s" % max(listNtraveltime))

    time.sleep(10)
    logging.debug("Simulation finished")
    traci.close()
    sys.stdout.flush()
    time.sleep(10)
	
    
	
 
 
                
def start_simulation(sumo, scenario, network, begin, end, interval, output):
    logging.debug("Finding unused port")
    print("Finding unused port")
    unused_port_lock = UnusedPortLock()
    unused_port_lock.__enter__()
    remote_port = find_unused_port()
    print("remote_port:{0}" .format(remote_port))
    logging.debug("Port %d was found" % remote_port)
    
    logging.debug("Starting SUMO as a server")
    
    sumo = subprocess.Popen(["D:\\E\\d\\sumo-0.25.0\\bin\\sumo.exe", "-c", "D:\\E\\d\\sumo-0.25.0\\bin\\los.sumo.cfg", "--tripinfo-output", output,"--device.emissions.probability", "1.0",  "--remote-port", str(remote_port)], stdout=sys.stdout, stderr=sys.stderr)    
    unused_port_lock.release()
            
    try:     
        traci.init(remote_port)    
        run(network, begin, end, interval)
    except Exception:
        logging.exception("Something bad happened")
    finally:
        logging.exception("Terminating SUMO")  
        terminate_sumo(sumo)
        unused_port_lock.__exit__()
        
def main():
    # Option handling
    parser = OptionParser(conflict_handler="resolve")#parser = OptionParser()
    parser.add_option("-c", "--command", dest="command", default="sumo", help="The command used to run SUMO [default: %default]", metavar="COMMAND")
    parser.add_option("-s", "--scenario", dest="scenario", default="los.sumo.cfg", help="A SUMO configuration file [default: %default]", metavar="FILE")
    parser.add_option("-n", "--network", dest="network", default="los.net.xml", help="A SUMO network definition file [default: %default]", metavar="FILE")    
    parser.add_option("-b", "--begin", dest="begin", type="int", default=200, action="store", help="The simulation time (s) at which the re-routing begins [default: %default]", metavar="BEGIN")
    #parser.add_option("-a", "--additional-files", dest="additional", default="UT.add.xml", help="Generate edge-based dump instead of ""lane-based dump. This is the default.", metavar="FILE")
    #parser.add_option("-a", "--additional-files", dest="additional", default="UTT.add.xml", help="Generate edge-based dump instead of ""lane-based dump. This is the default.", metavar="FILE")

    parser.add_option("-e", "--edge-based-dump", dest="edge_based_dump", action="store_true", default="True", help="Generate edge-based dump instead of ""lane-based dump. This is the default.", metavar="FILE")

    parser.add_option("-e", "--end", dest="end", type="int", default=72000, action="store", help="The simulation time (s) at which the re-routing ends [default: %default]", metavar="END")
    parser.add_option("-i", "--interval", dest="interval", type="int", default=200, action="store", help="The interval (s) at which vehicles are re-routed [default: %default]", metavar="INTERVAL")
    parser.add_option("-o", "--output", dest="output", default="mapnext.xml", help="The XML file at which the output must be written [default: %default]", metavar="FILE")

    parser.add_option("-l", "--logfile", dest="logfile", default=os.path.join(tempfile.gettempdir(), "next.log"), help="log messages to logfile [default: %default]", metavar="FILE")
    (options, args) = parser.parse_args()
    
    logging.basicConfig(filename=options.logfile, level=logging.DEBUG)
    logging.debug("Logging to %s" % options.logfile)
    
    if args:
        logging.warning("Superfluous command line arguments: \"%s\"" % " ".join(args))
        
    start_simulation(options.command, options.scenario, options.network, options.begin, options.end, options.interval, options.output)
    
if __name__ == "__main__":
    main()    
    
#"--device.hbefa.probability", "1.0",