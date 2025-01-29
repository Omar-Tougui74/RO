import tkinter as tk
from tkinter import ttk, messagebox
import matplotlib.pyplot as plt
import networkx as nx
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import random
import numpy as np
from PIL import Image, ImageTk
import heapq

# ===================== Configuration des couleurs modernes =====================
PRIMARY_COLOR = "#2c3e50"
SECONDARY_COLOR = "#3498db"
ACCENT_COLOR = "#e74c3c"
BACKGROUND_COLOR = "#ecf0f1"
TEXT_COLOR = "#2c3e50"

# ===================== Fonctions utilitaires =====================
def random_color():
    return "#{:06x}".format(random.randint(0, 0xFFFFFF))

def generate_random_costs(n_usines, n_magasins):
    return np.random.randint(1, 100, size=(n_usines, n_magasins))

def generate_random_capacities(n_usines):
    return np.random.randint(50, 200, size=n_usines)

def generate_random_demands(n_magasins):
    return np.random.randint(10, 100, size=n_magasins)

def initialiser_graphe(n):
    G = nx.DiGraph()
    nodes = [f"X{i}" for i in range(n)]
    G.add_nodes_from(nodes)
    for i in range(n):
        for j in range(n):
            if i != j and random.random() < 0.3:
                weight = random.randint(1, 100)
                G.add_edge(f"X{i}", f"X{j}", weight=weight)
    return G

def generer_graphe_flux(n):
    G = nx.DiGraph()
    nodes = [f"X{i}" for i in range(n)]
    G.add_nodes_from(nodes)
    for i in range(n):
        for j in range(n):
            if i != j and random.random() < 0.3:
                capacity = random.randint(1, 100)
                G.add_edge(f"X{i}", f"X{j}", capacity=capacity)
    return G

# ===================== Implémentations des algorithmes =====================
def dijkstra_personnalise(graph, start, end):
    distances = {node: float('infinity') for node in graph.nodes()}
    distances[start] = 0
    predecessors = {node: None for node in graph.nodes()}
    
    priority_queue = [(0, start)]
    
    while priority_queue:
        current_distance, current_node = heapq.heappop(priority_queue)
        
        if current_node == end:
            break
            
        if current_distance > distances[current_node]:
            continue
            
        for neighbor in graph.neighbors(current_node):
            weight = graph.get_edge_data(current_node, neighbor)['weight']
            distance = current_distance + weight
            
            if distance < distances[neighbor]:
                distances[neighbor] = distance
                predecessors[neighbor] = current_node
                heapq.heappush(priority_queue, (distance, neighbor))
    
    path = []
    current = end
    while current is not None:
        path.insert(0, current)
        current = predecessors.get(current, None)
    
    if not path or path[0] != start:
        raise nx.NetworkXNoPath(f"Aucun chemin entre {start} et {end}")
    
    return path, distances[end]

def bellman_ford_personnalise(graph, source):
    distances = {node: float('infinity') for node in graph.nodes()}
    predecessors = {node: None for node in graph.nodes()}
    distances[source] = 0

    for _ in range(len(graph.nodes()) - 1):
        for u, v in graph.edges():
            weight = graph.get_edge_data(u, v)['weight']
            if distances[u] + weight < distances[v]:
                distances[v] = distances[u] + weight
                predecessors[v] = u

    for u, v in graph.edges():
        weight = graph.get_edge_data(u, v)['weight']
        if distances[u] + weight < distances[v]:
            raise nx.NetworkXUnbounded("Cycle négatif détecté")

    return distances, predecessors

def ford_fulkerson_personnalise(graph, source, sink):
    def bfs(residual_graph, source, sink, parent):
        visited = {node: False for node in residual_graph.nodes()}
        queue = [source]
        visited[source] = True
        
        while queue:
            u = queue.pop(0)
            for v in residual_graph.neighbors(u):
                if not visited[v] and residual_graph[u][v]['capacity'] > 0:
                    queue.append(v)
                    visited[v] = True
                    parent[v] = u
                    if v == sink:
                        return True
        return False

    residual_graph = nx.create_empty_copy(graph)
    for u, v in graph.edges():
        residual_graph.add_edge(u, v, capacity=graph[u][v]['capacity'])
        residual_graph.add_edge(v, u, capacity=0)

    parent = {}
    max_flow = 0

    while bfs(residual_graph, source, sink, parent):
        path_flow = float('inf')
        s = sink
        
        while s != source:
            path_flow = min(path_flow, residual_graph[parent[s]][s]['capacity'])
            s = parent[s]

        max_flow += path_flow
        v = sink
        
        while v != source:
            u = parent[v]
            residual_graph[u][v]['capacity'] -= path_flow
            residual_graph[v][u]['capacity'] += path_flow
            v = u

    return max_flow

def generer_projet_pert(n_taches):
    G = nx.DiGraph()
    for i in range(n_taches):
        G.add_node(f"T{i}", duration=random.randint(1, 10))
    
    for i in range(n_taches):
        for j in range(i + 1, n_taches):
            if random.random() < 0.3:
                G.add_edge(f"T{i}", f"T{j}")
    
    if not nx.is_directed_acyclic_graph(G):
        return generer_projet_pert(n_taches)
    
    return G

def calculer_pert(graph):
    earliest_start = {node: 0 for node in graph.nodes}
    for node in nx.topological_sort(graph):
        for pred in graph.predecessors(node):
            if earliest_start[pred] + graph.nodes[pred]['duration'] > earliest_start[node]:
                earliest_start[node] = earliest_start[pred] + graph.nodes[pred]['duration']
    
    latest_finish = {node: earliest_start[max(earliest_start, key=earliest_start.get)] for node in graph.nodes}
    for node in reversed(list(nx.topological_sort(graph))):
        for succ in graph.successors(node):
            if latest_finish[succ] - graph.nodes[node]['duration'] < latest_finish[node]:
                latest_finish[node] = latest_finish[succ] - graph.nodes[node]['duration']
    
    total_float = {node: latest_finish[node] - (earliest_start[node] + graph.nodes[node]['duration']) for node in graph.nodes}
    
    critical_path = []
    current_node = max(earliest_start, key=earliest_start.get)
    while True:
        critical_path.append(current_node)
        predecessors = list(graph.predecessors(current_node))
        critical_preds = [pred for pred in predecessors if 
                         total_float[pred] == 0 and 
                         (earliest_start[pred] + graph.nodes[pred]['duration']) == earliest_start[current_node]]
        if not critical_preds:
            break
        current_node = critical_preds[0]
    
    critical_path.reverse()
    return {
        'earliest_start': earliest_start,
        'latest_finish': latest_finish,
        'total_float': total_float,
        'critical_path': critical_path,
        'duree_projet': max(earliest_start.values()) + max(graph.nodes[node]['duration'] for node in graph.nodes)
    }

# ===================== Classe principale de l'application =====================
class ModernORApp:
    def __init__(self, master):
        self.master = master
        self.master.title("Projet RO")
        self.master.geometry("1200x800")
        self.master.configure(bg=BACKGROUND_COLOR)
        
        self.style = ttk.Style()
        self.style.theme_use("clam")
        self.configure_styles()
        
        self.create_welcome_frame()
    
    def configure_styles(self):
        self.style.configure("TFrame", background=BACKGROUND_COLOR)
        self.style.configure("TButton", 
                           font=("Arial", 12, "bold"),
                           padding=10,
                           background=SECONDARY_COLOR,
                           foreground="white")
        self.style.map("TButton",
                      background=[("active", PRIMARY_COLOR), ("disabled", "#cccccc")],
                      foreground=[("disabled", "#666666")])
        
        self.style.configure("Header.TLabel", 
                           font=("Arial", 24, "bold"),
                           foreground=PRIMARY_COLOR,
                           background=BACKGROUND_COLOR)
        
        self.style.configure("Card.TFrame", 
                           background="white",
                           relief="raised",
                           borderwidth=2)
    
    def create_welcome_frame(self):
        self.welcome_frame = ttk.Frame(self.master)
        
        header = ttk.Frame(self.welcome_frame, style="Card.TFrame")
        header.pack(pady=40, padx=40, fill=tk.X)
        
        try:
            logo_img = ImageTk.PhotoImage(Image.open("C:/Users/tougu/Desktop/RO/emsilogo.jpg").resize((200, 100)))
            ttk.Label(header, image=logo_img).pack(side=tk.LEFT, padx=20)
            self.logo_img = logo_img
        except Exception as e:
            print(f"Erreur chargement logo: {e}")
            ttk.Label(header, text="EMSI", font=("Arial", 24, "bold"), foreground=PRIMARY_COLOR).pack(side=tk.LEFT, padx=20)
        
        title_frame = ttk.Frame(header)
        title_frame.pack(side=tk.LEFT, fill=tk.Y, pady=20)
        
        ttk.Label(title_frame , style="Header.TLabel").pack(pady=5)
        ttk.Label(title_frame, 
                text="Plateforme intelligente de l'implementation des algorithmes de Recherche Opérationnelle",
                font=("Arial", 14),
                foreground=TEXT_COLOR).pack()
        
        team_frame = ttk.Frame(self.welcome_frame, style="Card.TFrame")
        team_frame.pack(pady=20, padx=100, fill=tk.X)
        
        team_text = (
            "Encadré par : Dr. EL MKHALET Mouna\n\n"
            "Réalisé par :\n"
            "• Omar Tougui\n"
            "• Salma Boutarbouch"
        )
        ttk.Label(team_frame, 
                text=team_text,
                font=("Arial", 12),
                justify=tk.LEFT,
                background="white").pack(padx=20, pady=20)
        
        start_btn = ttk.Button(self.welcome_frame, 
                             text="Explorer les Algorithmes",
                             command=self.show_algorithm_selection)
        start_btn.pack(pady=40)
        
        self.welcome_frame.pack(expand=True, fill=tk.BOTH)
    
    def show_algorithm_selection(self):
        self.welcome_frame.pack_forget()
        
        self.algo_frame = ttk.Frame(self.master)
        
        for i in range(3):
            self.algo_frame.columnconfigure(i, weight=1)
        self.algo_frame.rowconfigure(0, weight=1)
        
        categories = {
            "Transport": ["Nord-Ouest", "Moindre Coût", "Stepping-Stone"],
            "Graphes": ["Welsh Powel", "Kruskal", "Dijkstra", "Bellman Ford"],
            "Réseaux": ["Ford Fulkerson", "Potentiel-Metra"]
        }
        
        for col, (category, algorithms) in enumerate(categories.items()):
            card = ttk.Frame(self.algo_frame, style="Card.TFrame")
            card.grid(row=0, column=col, padx=20, pady=20, sticky="nsew")
            
            ttk.Label(card, 
                    text=category,
                    font=("Arial", 16, "bold"),
                    foreground=ACCENT_COLOR).pack(pady=15)
            
            for algo in algorithms:
                btn = ttk.Button(card, 
                               text=algo,
                               command=lambda a=algo: self.show_algorithm_config(a))
                btn.pack(fill=tk.X, padx=10, pady=5)
        
        back_btn = ttk.Button(self.algo_frame, 
                            text="Retour",
                            command=self.return_to_welcome)
        back_btn.grid(row=1, column=1, pady=20)
        
        self.algo_frame.pack(expand=True, fill=tk.BOTH)
    
    def show_algorithm_config(self, algorithm):
        self.config_window = tk.Toplevel(self.master)
        self.config_window.title(f"Configuration - {algorithm}")
        self.config_window.geometry("500x400")
        self.center_window(self.config_window)
        
        main_frame = ttk.Frame(self.config_window)
        main_frame.pack(padx=20, pady=20, fill=tk.BOTH, expand=True)
        
        ttk.Label(main_frame, 
                text=f"Paramètres pour {algorithm}",
                font=("Arial", 14, "bold"),
                foreground=PRIMARY_COLOR).pack(pady=10)
        
        if algorithm in ["Nord-Ouest", "Moindre Coût", "Stepping-Stone"]:
            self.create_transport_inputs(main_frame, algorithm)
        else:
            self.create_graph_inputs(main_frame, algorithm)
        
        ttk.Button(main_frame, 
                 text="Exécuter",
                 command=lambda: self.execute_algorithm(algorithm)).pack(pady=20)
    
    def create_transport_inputs(self, parent, algorithm):
        input_frame = ttk.Frame(parent)
        input_frame.pack(pady=10, fill=tk.X)
        
        val = self.master.register(self.validate_number)
        
        ttk.Label(input_frame, text="Nombre d'usines:").grid(row=0, column=0, padx=5)
        self.n_usines = ttk.Entry(input_frame, font=("Arial", 12), validate="key", validatecommand=(val, '%P'))
        self.n_usines.grid(row=0, column=1, padx=5)
        
        ttk.Label(input_frame, text="Nombre de magasins:").grid(row=1, column=0, padx=5)
        self.n_magasins = ttk.Entry(input_frame, font=("Arial", 12), validate="key", validatecommand=(val, '%P'))
        self.n_magasins.grid(row=1, column=1, padx=5)
    
    def create_graph_inputs(self, parent, algorithm):
        input_frame = ttk.Frame(parent)
        input_frame.pack(pady=10, fill=tk.X)
        
        label_text = "Nombre de nœuds:" if algorithm != "Potentiel-Metra" else "Nombre de tâches:"
        ttk.Label(input_frame, text=label_text).grid(row=0, column=0, padx=5)
        self.n_nodes = ttk.Entry(input_frame, font=("Arial", 12))
        self.n_nodes.grid(row=0, column=1, padx=5)
    
    def validate_number(self, value):
        return value.isdigit() or value == ""
    
    def execute_algorithm(self, algorithm):
        try:
            if algorithm in ["Nord-Ouest", "Moindre Coût", "Stepping-Stone"]:
                n_usines = int(self.n_usines.get())
                n_magasins = int(self.n_magasins.get())
                result = self.run_transport_algorithm(algorithm, n_usines, n_magasins)
            else:
                valeur = int(self.n_nodes.get())
                result = self.run_graph_algorithm(algorithm, valeur)
            
            self.config_window.destroy()
            self.show_results(algorithm, result)
        except Exception as e:
            messagebox.showerror("Erreur", f"Entrée invalide: {str(e)}")

    def run_transport_algorithm(self, algo, n_usines, n_magasins):
        if algo == "Nord-Ouest":
            costs = generate_random_costs(n_usines, n_magasins)
            capacities = generate_random_capacities(n_usines)
            demands = generate_random_demands(n_magasins)
            allocation = coin_nord_ouest(capacities.copy(), demands.copy())
            total_cost = np.sum(allocation * costs)
            return {
                "type": "transport",
                "costs": costs,
                "capacities": capacities,
                "demands": demands,
                "allocation": allocation,
                "total_cost": total_cost
            }
        
        elif algo == "Moindre Coût":
            costs = generate_random_costs(n_usines, n_magasins)
            capacities = generate_random_capacities(n_usines)
            demands = generate_random_demands(n_magasins)
            
            costs_copy = costs.astype(float)
            capacities_copy = capacities.copy()
            demands_copy = demands.copy()
            
            allocation = algorithme_moindre_cout(costs_copy, capacities_copy, demands_copy)
            total_cost = np.sum(allocation * costs)
            
            return {
                "type": "transport",
                "costs": costs,
                "capacities": capacities,
                "demands": demands,
                "allocation": allocation,
                "total_cost": total_cost
            }
        
        elif algo == "Stepping-Stone":
            costs = generate_random_costs(n_usines, n_magasins)
            capacities = generate_random_capacities(n_usines)
            demands = generate_random_demands(n_magasins)
            allocation = stepping_stone(costs, capacities, demands)
            total_cost = np.sum(allocation * costs)
            return {
                "type": "transport",
                "costs": costs,
                "capacities": capacities,
                "demands": demands,
                "allocation": allocation,
                "total_cost": total_cost
            }

    def run_graph_algorithm(self, algo, valeur):
        if algo == "Welsh Powel":
            G = nx.gnp_random_graph(valeur, 0.5)
            coloring = nx.coloring.greedy_color(G, strategy='largest_first')
            return {
                "type": "graph",
                "graph": G,
                "coloring": coloring
            }
        
        elif algo == "Kruskal":
            G = nx.Graph()
            nodes = [f"X{i}" for i in range(valeur)]
            G.add_nodes_from(nodes)
            for i in range(valeur):
                for j in range(i + 1, valeur):
                    if random.random() < 0.3:
                        weight = random.randint(1, 100)
                        G.add_edge(f"X{i}", f"X{j}", weight=weight)
            mst = nx.minimum_spanning_tree(G, algorithm="kruskal")
            return {
                "type": "graph",
                "graph": G,
                "mst": mst
            }
        
        elif algo == "Dijkstra":
            G = initialiser_graphe(valeur)
            start = random.choice(list(G.nodes()))
            end = random.choice([n for n in G.nodes() if n != start])
            
            try:
                path, distance = dijkstra_personnalise(G, start, end)
                return {
                    "type": "graph",
                    "graph": G,
                    "start": start,
                    "end": end,
                    "path": path,
                    "distance": distance
                }
            except nx.NetworkXNoPath:
                return {
                    "type": "graph",
                    "graph": G,
                    "error": f"Aucun chemin entre {start} et {end}"
                }
        
        elif algo == "Bellman Ford":
            G = initialiser_graphe(valeur)
            start = random.choice(list(G.nodes()))
            try:
                distances, _ = bellman_ford_personnalise(G, start)
                return {
                    "type": "graph",
                    "graph": G,
                    "distances": distances,
                    "start": start
                }
            except nx.NetworkXUnbounded:
                return {
                    "type": "graph",
                    "graph": G,
                    "error": "Cycle négatif détecté"
                }
        
        elif algo == "Ford Fulkerson":
            G = generer_graphe_flux(valeur)
            source = "X0"
            sink = f"X{valeur-1}"
            try:
                max_flow = ford_fulkerson_personnalise(G, source, sink)
                return {
                    "type": "graph",
                    "graph": G,
                    "max_flow": max_flow,
                    "source": source,
                    "sink": sink
                }
            except Exception as e:
                return {
                    "type": "graph",
                    "graph": G,
                    "error": str(e)
                }
        
        elif algo == "Potentiel-Metra":
            try:
                G = generer_projet_pert(valeur)
                pert_data = calculer_pert(G)
                return {
                    "type": "graph",
                    "graph": G,
                    "pert_data": pert_data
                }
            except Exception as e:
                return {
                    "type": "graph",
                    "error": str(e)
                }
    
    def show_results(self, algorithm, data):
        result_window = tk.Toplevel(self.master)
        result_window.title(f"Résultats - {algorithm}")
        result_window.geometry("1000x700")
        self.center_window(result_window)
        
        notebook = ttk.Notebook(result_window)
        
        if data["type"] == "graph" and "graph" in data:
            viz_frame = ttk.Frame(notebook)
            self.create_graph_visualization(viz_frame, algorithm, data)
            notebook.add(viz_frame, text="Visualisation")
        
        summary_frame = ttk.Frame(notebook)
        self.create_summary_tab(summary_frame, algorithm, data)
        notebook.add(summary_frame, text="Résumé")
        
        notebook.pack(expand=True, fill=tk.BOTH)
    
    def create_summary_tab(self, parent, algorithm, data):
        text_area = tk.Text(parent, wrap=tk.WORD, font=("Consolas", 12))
        scrollbar = ttk.Scrollbar(parent, command=text_area.yview)
        text_area.configure(yscrollcommand=scrollbar.set)
        
        text_content = ""
        
        if data["type"] == "transport":
            text_content = f"""Coûts de transport:
{data['costs']}

Capacités des usines:
{data['capacities']}

Demandes des magasins:
{data['demands']}

Allocation:
{data['allocation']}

Coût total: {data['total_cost']}"""
        
        elif data["type"] == "graph":
            if "coloring" in data:
                text_content = f"Coloration des sommets:\n{data['coloring']}"
            elif "mst" in data:
                text_content = "Arbre couvrant minimal (Kruskal):\n"
                text_content += "\n".join(f"{u}-{v} (euro: {d['weight']})" 
                                        for u, v, d in data['mst'].edges(data=True))
            elif "path" in data:
                text_content = f"Plus court chemin (Dijkstra):\n"
                text_content += f"Départ: {data['start']}\nArrivée: {data['end']}\n"
                text_content += f"Chemin: {' -> '.join(data['path'])}\n"
                text_content += f"Distance totale: {data['distance']}"
            elif "distances" in data:
                text_content = f"Distances depuis {data['start']}:\n"
                for node, dist in data["distances"].items():
                    text_content += f"{node}: {dist}\n"
            elif "max_flow" in data:
                text_content = f"Flot maximal de {data['source']} à {data['sink']}: {data['max_flow']}"
            elif "pert_data" in data:
                text_content = "=== Méthode Potentiel-Métra ===\n"
                text_content += f"Durée totale du projet: {data['pert_data']['duree_projet']}\n"
                text_content += "Chemin critique:\n"
                text_content += " -> ".join(data['pert_data']['critical_path']) + "\n\n"
                text_content += "Détails par tâche:\n"
                for node in data['graph'].nodes():
                    text_content += (
                        f"Tâche {node} - Durée: {data['graph'].nodes[node]['duration']}\n"
                        f"ES: {data['pert_data']['earliest_start'][node]} | "
                        f"LF: {data['pert_data']['latest_finish'][node]} | "
                        f"Marge: {data['pert_data']['total_float'][node]}\n\n"
                    )
            elif "error" in data:
                text_content = data["error"]
        
        text_area.insert(tk.END, text_content)
        text_area.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
    
    def create_graph_visualization(self, parent, algorithm, data):
        plt.style.use('ggplot')
        fig = plt.figure(figsize=(10, 8))
        G = data["graph"]
        pos = nx.spring_layout(G, seed=42)
        
        if algorithm == "Kruskal":
            mst = data["mst"]
            nx.draw(G, pos, with_labels=True,
                   node_color=SECONDARY_COLOR,
                   edge_color="#cccccc",
                   node_size=800,
                   font_weight='bold')
            nx.draw_networkx_edges(mst, pos,
                                  edgelist=mst.edges(),
                                  edge_color=ACCENT_COLOR,
                                  width=3)
            nx.draw_networkx_nodes(mst, pos,
                                  nodelist=mst.nodes(),
                                  node_color=ACCENT_COLOR,
                                  node_size=800)
        
        elif algorithm == "Welsh Powel":
            color_palette = ['#FF6B6B', '#4ECDC4', '#45B7D1', '#96CEB4', '#FFEEAD', '#D4A5A5']
            node_colors = [color_palette[data['coloring'][node] % len(color_palette)] 
                          for node in G.nodes()]
            nx.draw(G, pos, with_labels=True,
                   node_color=node_colors,
                   node_size=800,
                   edge_color='#666666',
                   font_weight='bold',
                   edgecolors='black')
        
        elif algorithm == "Dijkstra":
            edge_labels = nx.get_edge_attributes(G, 'weight')
            path_edges = list(zip(data["path"], data["path"][1:]))
            nx.draw(G, pos, with_labels=True,
                   node_color=SECONDARY_COLOR,
                   node_size=800,
                   edge_color='#666666',
                   font_weight='bold')
            nx.draw_networkx_edge_labels(G, pos, edge_labels=edge_labels)
            nx.draw_networkx_edges(G, pos,
                                  edgelist=path_edges,
                                  edge_color=ACCENT_COLOR,
                                  width=3)
        
        elif algorithm == "Potentiel-Metra":
            critical_path = data['pert_data']['critical_path']
            path_edges = list(zip(critical_path, critical_path[1:]))
            node_colors = [ACCENT_COLOR if node in critical_path else SECONDARY_COLOR for node in G.nodes()]
            edge_colors = [ACCENT_COLOR if (u, v) in path_edges else PRIMARY_COLOR for u, v in G.edges()]
            nx.draw(G, pos, with_labels=True,
                   node_color=node_colors,
                   edge_color=edge_colors,
                   width=2,
                   node_size=800,
                   font_weight='bold',
                   edgecolors='black')
            edge_labels = {(u, v): G.nodes[v]['duration'] for u, v in G.edges()}
            nx.draw_networkx_edge_labels(G, pos, edge_labels=edge_labels)
        
        else:
            nx.draw(G, pos, with_labels=True,
                   node_color=SECONDARY_COLOR,
                   node_size=800,
                   font_weight='bold',
                   edge_color='#666666')
        
        plt.title("Visualisation du graphe", fontsize=14, pad=20)
        canvas = FigureCanvasTkAgg(fig, master=parent)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
    
    def center_window(self, window):
        window.update_idletasks()
        width = window.winfo_width()
        height = window.winfo_height()
        x = (self.master.winfo_screenwidth() // 2) - (width // 2)
        y = (self.master.winfo_screenheight() // 2) - (height // 2)
        window.geometry(f'{width}x{height}+{x}+{y}')
    
    def return_to_welcome(self):
        self.algo_frame.pack_forget()
        self.welcome_frame.pack(expand=True, fill=tk.BOTH)

# ===================== Algorithmes de transport =====================
def coin_nord_ouest(capacities, demands):
    allocation = np.zeros((len(capacities), len(demands)), dtype=int)
    i, j = 0, 0
    while i < len(capacities) and j < len(demands):
        quantity = min(capacities[i], demands[j])
        allocation[i][j] = quantity
        capacities[i] -= quantity
        demands[j] -= quantity
        if capacities[i] == 0:
            i += 1
        else:
            j += 1
    return allocation

def algorithme_moindre_cout(costs, capacities, demands):
    costs = costs.astype(float)
    allocation = np.zeros_like(costs, dtype=int)
    
    while np.sum(capacities) > 0 and np.sum(demands) > 0:
        masked_costs = np.where(costs == np.inf, np.nan, costs)
        if np.all(np.isnan(masked_costs)):
            break
            
        i, j = np.unravel_index(np.nanargmin(masked_costs), costs.shape)
        
        if np.isinf(costs[i, j]) or capacities[i] == 0 or demands[j] == 0:
            break
            
        quantity = min(capacities[i], demands[j])
        allocation[i][j] = quantity
        capacities[i] -= quantity
        demands[j] -= quantity
        
        if capacities[i] == 0:
            costs[i, :] = np.inf
        if demands[j] == 0:
            costs[:, j] = np.inf
            
    return allocation

def stepping_stone(costs, capacities, demands):
    allocation = coin_nord_ouest(capacities.copy(), demands.copy())
    return allocation

# ===================== Lancement de l'application =====================
if __name__ == "__main__":
    root = tk.Tk()
    app = ModernORApp(root)
    root.mainloop()