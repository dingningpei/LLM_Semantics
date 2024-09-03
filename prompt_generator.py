import rdflib
import json

def extract_properties(graph):
    """Extract rdf:Property, rdfs:domain, and rdfs:range from the graph."""
    properties = []
    for s, p, o in graph.triples((None, rdflib.RDF.type, rdflib.RDF.Property)):
        domain = list(graph.objects(s, rdflib.RDFS.domain))
        range_ = list(graph.objects(s, rdflib.RDFS.range))
        properties.append({
            "property": str(s),
            "domain": [str(d) for d in domain],
            "range": [str(r) for r in range_]
        })
    return properties


def load_ontologies(file_path):
    """Load ontologies from a JSON file."""
    with open(file_path, 'r', encoding='utf-8') as file:
        ontologies = json.load(file)
    return ontologies

def generate_prompt_without_semantic_typing(train_data, ontologies, with_inst=False):
    """Generate a prompt for the LLM based on the table data and ontologies."""
    #And the number of entities has to strictly have the same value as the number of respective relation.

    #  "Given the table, please find the semantic graph of the table in the strict format of given examples above. In this task, we use a set of triples to represent the semantic graph of the table, \
    #         where each triple has the form of (subject, predicate, object). The subject and object have to be chosen from the nodes in the ontologies, and the predicate has to be chosen from the properties in the ontologies. \
    #         The symbol '->' in the ontologies is used to represent the 'is parent class of' relation. The ontologies are provided below:"
    prompt_insts = ""
    if with_inst:
        prompt_insts = "Given the table, please find the semantic graph of the table in the strict format of given examples above. In this task, we use two sets of triples to represent the semantic graph of the table: the SetSemanticType part is a set of triples to construte semantic typing which links the columns in table to the nodes and the SetInternalLink part is a set of triples to construct the links between internal nodes.  \
            where each triple has the form of (subject, predicate, object). The subject and object have to be chosen from the nodes in the ontologies, and the predicate has to be chosen from the properties in the ontologies. \
            The symbol '->' in the ontologies is used to represent the 'is parent class of' relation. The ontologies are provided below:"
        for ontology_name, ontology_data in ontologies.items():
            for node in ontology_data['Nodes']:
                prompt_insts += f"(Node: {node}), "
            for prop in ontology_data['Properties']:
                prompt_insts += f"(Property: {prop}), "
    else:
        prompt_insts = """Given the table, please find the corresponding semantic of the table and their corresponding relation types in the strict format of given examples above (note that the number of entities has to strictly have the same value as the number of respective relation): """

    prompt = "I will provide examples of tables and their corresponding semantic graphs below. Each table is a list of dictionaries, where each dictionary represents a row of the table, and the key-value pairs are the column names and their corresponding values.\n"
    for i, data in enumerate(train_data):
        prompt += f"Table{i}: "
        for j, table in enumerate(data['table']):
            prompt += f"{table}\n"
        prompt += f"The semantic graph of the table: {data['semantic_graph']}\n"
    prompt += prompt_insts
    return prompt

