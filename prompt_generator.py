import rdflib

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


def load_ontology(file_path):
    """Load the ontology from an RDF file."""
    g = rdflib.Graph()
    g.parse(file_path, format="xml")
    return g


def generate_prompt_without_semantic_typing(train_data, ontology, with_inst=False):
    """Generate a prompt for the LLM based on the table data and ontology."""
    prompt_insts = ""
    if with_inst:
        # "What is the semantic information and data source relationship DOT file for the new table?"
        prompt_insts = "Given the table, please find the semantic graph of the table \
types in the strict format of given examples above, please only strictly choose from the following rdf relations \
types in Ontologies constraints: "
        # to-do
        # add the ontology owl file into the prompt to constrain the knowledge extraction
        for s, p, o in ontology.triples((None, rdflib.RDF.type, rdflib.RDF.Property)):
            domain = list(ontology.objects(s, rdflib.RDFS.domain))
            range_ = list(ontology.objects(s, rdflib.RDFS.range))
            prompt_insts += f"(Property: {str(s)}, Domain: {str(domain[0])}, Range: {str(range_[0])}), "
    else:
        prompt_insts = """Given the table, please find the corresponding semantic of the table and their corresponding relation \
types in the strict format of given examples above (note that the number of entities has to strictly have the same value as the number of respective relation): """

    prompt = "The tables following are in the json style. Each json file contains column names and their corresponding one row data.\n"
    for i, data in enumerate(train_data):
        prompt += f"Table{i}: "
        for j, table in enumerate(data['table']):
            prompt += f"{table}\n"
        prompt += f"The semantic graph of the table in the strict format of given examples above: {data['semantic_graph']}\n"
    prompt += prompt_insts
    return prompt

