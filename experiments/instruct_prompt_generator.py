import json

def load_ontologies(file_path):
    """Load ontologies from a JSON file."""
    with open(file_path, 'r', encoding='utf-8') as file:
        ontologies = json.load(file)
    return ontologies

def generate_instruct_prompt(train_data, ontologies, with_inst=False):
    system_prompt = "The user will provide tables in a JSON format and the system will output the semantic graphs of the tables in the strict format of examples users provided. Each table is a list of dictionaries, where each dictionary represents a row of the table, and the key-value pairs are the column names and their corresponding values. \
The semantic graph should be two lists of triples: SetSemanticType and SetInternalLink. SetSemanticType is a list of triples that link all the columns in table(even though one column in the table may have multiple values, the system should treat these multiple values as one column) to the nodes in ontology, \
and SetInternalLink is a list of triples that link the nodes in semantic graph to each other. \
Each triple has the form of (subject, predicate, object). To generate the semantic graph from the provided table, the system should follow a structured process that involves mapping the table columns to ontological concepts and establishing relationships between these concepts, must not seperate the column into different SemanticType, and do not ignore the columns whose value  <Empty>. Here's a step-by-step breakdown of how the system do this. \n\
Step 1: Identify Semantic Types \n\
The system will identify the appropriate semantic types from nodes in the ontology for each column in the table. The system will not ignore any columns in the table without exception. If the data in the column is <Empty>, the system will only take the column name into consideration to find the appropriate semantic types from nodes in the ontology.\n\
Step 2: Establish Internal Links \n\
The system will establish internal links between the semantic types based on the properties defined in the ontology and the nodes in the ontology. \n\
Step 3: Construct the Semantic Graph \n\
Using the identified semantic types and established internal links, the system will construct the semantic graph. This graph consists of two main components: \n\
1. SetSemanticType: A list of triples that link the columns in the table to the nodes in the ontology. Each triple has the form (subject, predicate, object), where the subject is the semantic type, the predicate is the property linking the subject to the object, and the object is the column in the table. \n\
2. SetInternalLink: A list of triples that link the nodes in the semantic graph to each other. Each triple has the form (subject, predicate, object), where the subject and object are nodes in the ontology, and the predicate is the property in the ontology defining the relationship between them. \n"
    system_prompt += "The symbol '->' in the ontology is used to represent the 'is parent class of' relation. \n"
    nodes = []
    properties = []
    potential_triples = []
    system_prompt += f"Ontology:\n"
    for ontology_name, ontology_data in ontologies.items():
        for node in ontology_data['Nodes']:
            nodes.append(node)
        for prop in ontology_data['Properties']:
            properties.append(prop)
        for triples in ontology_data['Potential triples']:
            potential_triples.append(triples.replace("<", "[").replace(">", "]"))
    system_prompt += f"Nodes: {nodes}\n"
    system_prompt += f"Properties: {properties}\n"
    system_prompt += f"Potential triples: {potential_triples}\n"
    message = [
        {"role": "system", "content": system_prompt}
    ]
    for i, data in enumerate(train_data):
        message.append({"role": "user", "content": f"Table: {data['table']}"})   
        message.append({"role": "assistant", "content": f"{data['semantic_graph']}"})
    return message





# def generate_instruct_prompt(train_data, ontologies, with_inst=False):
#     system_prompt = "The user will provide tables in a JSON format and the system will output the semantic graphs of the tables in the strict format of examples users provided. Each table is a list of dictionaries, where each dictionary represents a row of the table, and the key-value pairs are the column names and their corresponding values. \
# The semantic graph should be two lists of triples: SetSemanticType and SetInternalLink. SetSemanticType is a list of triples that link all the columns in table(even though one column in the table may have multiple values, the system should treat these multiple values as one column) to the nodes in ontology, \
# # and SetInternalLink is a list of triples that link the nodes in semantic graph to each other. \
# Each triple has the form of (subject, predicate, object). The system should do two steps to output the semantic graph: \n\
# Step 1 Find the SetSemanticType triples: \
# In this step,the system must not ignore any columns in the table without exception and no matter weather the values of the column are empty stringsor not. The system will frist try to map the columns in the table to the potential triples in the ontology whose object is start with http://www.w3.org/2000/01/rdf-schema# and replace the objects with the columns in the table. \
# Then if there is any columns in the table that can not be mapped directly to the potential triples in the ontology, for these columns, the system will find the most suitable nodes in the ontology as the object of the SetSemanticType triple and the most suitable properties in the ontology linking these nodes and these columns as the predicate of the SetSemanticType triples. \
# These columns will be subject of the SetSemanticType triples. And finally, the system will construct the rest of the SetSemanticType triples for the columns left. \\n\
# Step 2 Find the SetInternalLink triples: \
# In this step, the system will take the table and the SetSemanticType triples as the input to find the SetInternalLink triples. The system should then search potential triples in the ontology to find part of or the whole SetInternalLink triples. Then using the information from the part of SetInternalLink triples found, the system will construct the rest of the SetInternalLink triples follow the following rules. \
# The subject of each triple has to be chosen from the nodes in ontology, and the object of each triple has to be chosen from the nodes in the ontology. The predicate of each triple has to be chosen from the properties in the ontology. "
#     system_prompt += "The symbol '->' in the ontology is used to represent the 'is parent class of' relation. \n"
#     for ontology_name, ontology_data in ontologies.items():
#         system_prompt += f"Ontology: {ontology_name}\n"
#         for node in ontology_data['Nodes']:
#             system_prompt += f"(Node: {node}), "
#         for prop in ontology_data['Properties']:
#             system_prompt += f"(Property: {prop}), "
#         for potential_triples in ontology_data['Potential triples']:
#             system_prompt += f"(Potential triples: {potential_triples}), "
#     message = [
#         {"role": "system", "content": system_prompt}
#     ]
#     for i, data in enumerate(train_data):
#         message.append({"role": "user", "content": f"Table: {data['table']}"})   
#         message.append({"role": "assistant", "content": f"{data['semantic_graph']}"})
#     return message

# def generate_instruct_prompt(train_data, ontologies, with_inst=False):
#     system_prompt = "The user will provide tables in a JSON format and the system will output the semantic graphs of the tables in the strict format of examples users provided. Each table is a list of dictionaries, where each dictionary represents a row of the table, and the key-value pairs are the column names and their corresponding values. \
# The semantic graph should be two lists of triples: SetSemanticType and SetInternalLink. SetSemanticType is a list of triples that link all the columns in table(even though one column in the table may have multiple values, the system should treat these multiple values as one column) to the nodes in ontologies, \
# and SetInternalLink is a list of triples that link the nodes in semantic graph to each other. \
# Each triple has the form of (subject, predicate, object). The system should do two steps to output the semantic graph: \n\
# 1. Find the SetSemanticType triples: \
# In this step, the system will take the table as the input to find the SetSemanticType triples for all the columns in the table. And the system can not ignore any columns in the table without exception and no matter what the values of the column are. \
# When one column in the table may contains multiple values which represent different types of information, the system should not separate the values into multiple columns to make sure that the number of the SetSemanticType triples is the same as the number of the columns in the table.  \
# The system should first search potential triples in the ontologies whose object is start with http://www.w3.org/2000/01/rdf-schema# to find part of or the whole SetSemanticType triples and replace the objects with the columns in the table. Then using the information from the part of SetSemanticType triples found, complete the rest of the SetSemanticType triples follow the following rules and \
# The subject of each triple has to be chosen from the nodes in ontologies, and the object of each triple has to be chosen from the columns in the table. \
# The predicate of each triple has to be chosen from the properties in the ontologies. \n\
# 2. Find the SetInternalLink triples: \
# In this step, the system will take the table and the SetSemanticType triples as the input to find the SetInternalLink triples. The system should then search potential triples in the ontologies to find part of or the whole SetInternalLink triples. Then using the information from the part of SetInternalLink triples found, complete the rest of the SetInternalLink triples follow the following rules. \
# The subject of each triple has to be chosen from the nodes in ontologies, and the object of each triple has to be chosen from the nodes in the ontologies. The predicate of each triple has to be chosen from the properties in the ontologies. "
#     system_prompt += "The symbol '->' in the ontology is used to represent the 'is parent class of' relation. \n"
#     for ontology_name, ontology_data in ontologies.items():
#         system_prompt += f"Ontology: {ontology_name}\n"
#         for node in ontology_data['Nodes']:
#             system_prompt += f"(Node: {node}), "
#         for prop in ontology_data['Properties']:
#             system_prompt += f"(Property: {prop}), "
#         for potential_triples in ontology_data['Potential triples']:
#             system_prompt += f"(Potential triples: {potential_triples}), "
#     message = [
#         {"role": "system", "content": system_prompt}
#     ]
#     for i, data in enumerate(train_data):
#         message.append({"role": "user", "content": f"Table: {data['table']}"})   
#         message.append({"role": "assistant", "content": f"{data['semantic_graph']}"})
#     return message