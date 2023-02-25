FROM python:3.9-buster
WORKDIR /app

COPY requirements.txt .
RUN pip install -r requirements.txt

COPY . .

RUN apt-get update && apt-get install -y coq
# RUN git clone https://github.com/UniMath/UniMath && git checkout tags/v20220204 && cd UniMath && make Foundations -j 8 && cd ..

CMD ["python", "webapp/app.py"]